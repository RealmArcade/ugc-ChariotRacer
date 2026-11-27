namespace Realm.Maps;

using System;
using System.Collections.Generic;
using System.Numerics;
using Realm.Ecs;
using Realm.Ecs.Components.Core;
using Realm.MapAPI;

public class MapScript : IWasmModule
{
    private static readonly int[] LapOptions = { 1, 2, 3, 5 };
    private int lapOption = 2;
    private int Laps => LapOptions[lapOption];
    private const string PickLaps = "ability/garage_laps", PickCar = "ability/garage_car", StartRace = "ability/garage_start";
    private static readonly string[] Cars = { UnitIds.ChariotRacer, "unit/aguja", "unit/mastodonte" };
    private sealed record CarProfile(string Name, int Strength, int Agility, int Armor);
    private static readonly CarProfile[] Profiles = {
        new("Ember", 3, 3, 3), new("Needle", 2, 4, 3), new("Mastodon", 3, 2, 4)
    };
    private bool garage;
    private float garageTime;
    private const float LaneWidth = 5f;
    private const float RoadEdge = 1.5f * LaneWidth;
    private const float ShoulderEdge = RoadEdge + 3.75f;
    private const int SamplesPerBend = 12;
    private const float CruiseSpeed = 20.5f;
    private const float BoostSpeed = 32.5f;
    private const float LaunchSpeed = 21f;
    private const float GateLookAhead = 31f;
    private const float GapWidth = 8;
    private const float DraftSeconds = 1.5f;
    private const float BumperSpacing = 1.45f;
    private const string CrystalAbility = AbilityIds.Holylight;
    private const string RepairAbility = "ability/coin_repair";
    private const int RepairCost = 3;
    private enum Power { None, Grip, Shield, FrostBolt, Disruptor, Shockwave, Blackout, Mine, Winterlock }
    private const int MineCharges = 4;
    private const float FreezeSeconds = 5;
    private float nextWinterlock;
    private static readonly (Power Item, int First, int Last)[] CrystalOdds = {
        (Power.Grip, 30, 6), (Power.Shield, 30, 9), (Power.FrostBolt, 8, 10),
        (Power.Disruptor, 8, 10), (Power.Shockwave, 3, 18), (Power.Blackout, 3, 15),
        (Power.Mine, 18, 7), (Power.Winterlock, 0, 25)
    };
    private sealed record Part(string Ability, string Name);
    private static readonly Part Stock = new("", "Stock");
    private static readonly Part Axle = new("ability/scout_axle", "Scout Axle");
    private static readonly Part Plating = new("ability/stoneguard_plating", "Stoneguard Plating");
    private static readonly Part Suspension = new("ability/reinforced_suspension", "Reinforced Suspension");
    private static readonly Part[] Workshop = { Axle, Plating, Suspension };
    private sealed class Pickup
    {
        public Vector3 Position;
        public UnitId Model;
        public bool IsCoin;
        public float Facing;
        public float RespawnAt;
    }
    private static readonly Vector3 Cyan = new(0.15f, 0.95f, 1);
    private static readonly Vector3 Amber = new(1, 0.46f, 0.12f);

    private sealed class Racer
    {
        public UnitId Unit;
        public int Seat, Lane, NextGate;
        public bool Computer, Charged = true;
        public float Distance, Offset, Speed, Boost, Drag, Finish = float.PositiveInfinity;
        public int PlannedGate = -1;
        public int AnnouncedGate = -1;
        public Racer? Ahead;
        public float Gap, Draft, DecisionDelay, LapStart, BestLap = float.PositiveInfinity;
        public float FrameDistance, FrameOffset, FrameSpeed;
        public bool FrameFinished;
        public bool LaunchAttempted, LaunchReady, StartedLap;
        public float Runout;
        public bool LeftHeld, RightHeld;
        public bool Withdrawn;
        public float Heading, TravelHeading, YawRate, Steering, RearSlip;
        public Part Installed = Stock;
        public CarProfile Profile => Profiles[Car];
        public float AccelerationScale => (1 + 0.05f * (Profile.Strength - 3)) *
            (Installed == Axle ? 0.95f : Installed == Plating ? 0.94f : 1);
        public float RecoveryTime => Math.Max(0.90f, (1 - 0.05f * (Profile.Agility - 3)) *
            (Installed == Axle ? 0.92f : 1));
        public float ImpactTime => Math.Max(0.75f, (1 - 0.10f * (Profile.Armor - 3)) *
            (Installed == Plating ? 0.80f : 1));
        public float LandingSlip;
        public int Integrity = 100, Coins;
        public float EngineSpeedScale => 0.12f + 0.88f * (Integrity / 100f);
        public bool GarageInputReceived;
        public Power StoredPower;
        public int Charges;
        public float FrozenUntil, NextBotMine;
        public Vector3 WorldPosition;
        public float GripUntil, ShieldUntil, JamUntil;
        public Racer? Target;
        public float Checkpoint, JumpLip, FlightTime, FlightHeight, TakeoffHeight, AirForward, AirSide;
        public bool Flying, OnLaunchPad;
        public string DriveAnimation = "";
        public int CompletedLaps, Car;
        public string Name = "";
    }

    private readonly record struct Gate(float Distance, int Lane);
    private readonly List<Racer> racers = new();
    private readonly List<Vector2> road = new();
    private readonly List<float> lengths = new();
    private readonly List<Vector2> normals = new();
    private readonly List<Gate> gates = new();
    private readonly List<float> waypoints = new();
    private readonly List<float> jumpLips = new();
    private readonly List<(float Start, int Side)> cliffEdges = new();
    private readonly record struct Mine(Vector3 Position, int Owner, float Expires, int Sign);
    private readonly List<Mine> mines = new();
    private readonly List<Pickup> pickups = new();
    private readonly string[] boardRows = new string[8];
    private IGameAPI game = null!;
    private float Length => lengths[^1];
    private float clock, nextBoard;
    private int countdownDigit, startSign;
    private float nextPickupCheck;
    private bool ended;
    private float podiumUntil;

    public void Initialize(IGameAPI api)
    {
        game = api;
        game.DisableShroud();
        game.SetDayNightCycleEnabled(false);
        game.SetTimeOfDay(15);
        BuildRoad();
        if (road.Count == 0)
        {
            game.BroadcastMessage("The circuit requires at least four consecutive regions starting at waypoint_01.");
            ended = true;
            return;
        }

        for (int seat = 1; seat <= 8; seat++)
            if (game.GetPlayer(seat).IsActive)
                AddRacer(seat, IsComputer(seat));

        game.OnSpellCast += OnAbility;
        game.OnPlayerLeft += seat => {
            var racer = racers.Find(r => r.Seat == seat);
            if (racer == null || racer.Withdrawn || float.IsFinite(racer.Finish)) return;
            racer.Withdrawn = true;
            game.DestroyUnit(racer.Unit, false, false);
            if (garage) RefreshGarage();
        };
        clock = -5;
        garage = Director() != null;
        PlaceRacePickups();
        if (garage) RefreshGarage();
        else OpenRace();
    }

    private static unsafe bool IsComputer(int seat) =>
        EcsSharedMemory.GetComponent<ScriptPlayer>(ComponentIds.ScriptPlayer, seat)->IsComputer;

    // The editor regions define the racing line. waypoint_01 is the finish.
    private void BuildRoad()
    {
        var nodes = new List<Vector2>();
        for (int i = 1; game.TryGetCoordinate($"waypoint_{i:00}", out var region); i++)
        {
            var p = (region.Min + region.Max) * 0.5f;
            nodes.Add(new(p.X, p.Z));
        }
        if (nodes.Count < 4) return;
        int n = nodes.Count;
        float distance = 0;
        for (int i = 0; i < n; i++)
        {
            Vector2 a = nodes[(i + n - 1) % n], b = nodes[i];
            Vector2 c = nodes[(i + 1) % n], d = nodes[(i + 2) % n];
            for (int j = 0; j < SamplesPerBend; j++)
            {
                float t = (float)j / SamplesPerBend;
                Vector2 p = 0.5f * (2*b + (c-a)*t + (2*a-5*b+4*c-d)*t*t + (3*b-a-3*c+d)*t*t*t);
                if (road.Count > 0)
                {
                    float step = Vector2.Distance(road[^1], p);
                    if (step < 0.001f) continue;
                    distance += step;
                }
                road.Add(p);
                lengths.Add(distance);
                if (j == 0)
                {
                    waypoints.Add(distance);
                    if (game.TryGetCoordinate($"jump_{i+1:00}", out _)) jumpLips.Add(distance + 14);
                    if (game.TryGetCoordinate($"right_cliff_{i+1:00}", out _)) cliffEdges.Add((distance, 1));
                    if (game.TryGetCoordinate($"left_cliff_{i+1:00}", out _)) cliffEdges.Add((distance, -1));
                }
                if (j == 0 && i % 3 == 2)
                    gates.Add(new(distance, (i / 3 + 2) % 3 - 1));
            }
        }
        if (road.Count < 4) { road.Clear(); return; }
        lengths.Add(distance + Vector2.Distance(road[^1], road[0]));
        road.Add(road[0]);
        for (int i = 0; i < road.Count - 1; i++)
        {
            Vector2 tangent = Vector2.Normalize(road[i + 1] - road[(i + road.Count - 2) % (road.Count - 1)]);
            normals.Add(new(-tangent.Y, tangent.X));
        }
        normals.Add(normals[0]);
        gates.Insert(0, new(22, -1)); // A choice of lanes on the opening straight.
        Stripe(0, -RoadEdge, RoadEdge, Vector3.One, 0.5f);
    }

    private static int HazardLane(Gate g) => g.Lane == 1 ? -1 : g.Lane + 1;

    private Vector2 Sample(float distance, float offset, out Vector2 forward)
    {
        float s = distance % Length;
        if (s < 0) s += Length;
        int i = lengths.BinarySearch(s);
        if (i < 0) i = ~i - 1;
        i = Math.Clamp(i, 0, road.Count - 2);
        float t = (s - lengths[i]) / (lengths[i + 1] - lengths[i]);
        Vector2 normal = Vector2.Normalize(Vector2.Lerp(normals[i], normals[i + 1], t));
        forward = new(normal.Y, -normal.X);
        return Vector2.Lerp(road[i], road[i + 1], t) + normal * offset;
    }

    private void Stripe(float distance, float left, float right, Vector3 color, float width) =>
        game.DrawLineOnTerrain(Sample(distance, left, out _), Sample(distance, right, out _), color, 3600, width);

    private void AddRacer(int seat, bool computer)
    {
        // Project the authored grid onto the approach straight, keeping its head start and lane.
        Vector3 anchor = game.GetSpawnAnchor(seat);
        Vector2 origin = Sample(0, 0, out var forward);
        Vector2 delta = new Vector2(anchor.X, anchor.Z) - origin;
        float offset = Vector2.Dot(delta, new(-forward.Y, forward.X));
        var r = new Racer { Seat = seat, Computer = computer, Name = game.GetPlayerName(seat),
            Lane = Math.Clamp((int)MathF.Round(offset / LaneWidth), -1, 1),
            Distance = Math.Clamp(Vector2.Dot(delta, forward), -24, -1) };
        r.Offset = r.Lane * LaneWidth;
        Vector2 start = Sample(r.Distance, r.Offset, out var startDirection);
        r.Heading = MathF.Atan2(startDirection.X, startDirection.Y);
        r.TravelHeading = r.Heading;
        r.Unit = game.SpawnUnitForPlayer(Cars[0], start, seat, executeSpawnShader: false, bypassPopulation: true);
        if (!r.Unit.IsValid) return;
        racers.Add(r);
        ConfigureCar(r);
        game.SetPlayerGold(seat, 0);
        game.SetPlayerWood(seat, 0);
        game.SetPlayerStone(seat, 0);
    }

    private void ConfigureCar(Racer r)
    {
        r.Unit.Invulnerable = true;
        game.SetUnitCommandsFrozen(r.Unit, true);
        r.Unit.Speed = 0;
        r.Unit.HideHealthAndManaBars = false;
        game.SetUnitMaxHealth(r.Unit, 100);
        game.SetUnitMaxMana(r.Unit, 100);
        game.SetUnitManaRegen(r.Unit, 0);
        game.SetUnitHealth(r.Unit, r.Integrity);
        game.SetUnitMana(r.Unit, 0);
        game.SetAbilityState(r.Unit, AbilityIds.SteerLeftStop, false, true);
        game.SetAbilityState(r.Unit, AbilityIds.SteerRightStop, false, true);
        game.SetAbilityState(r.Unit, CrystalAbility, true, false);
        game.SetAbilityState(r.Unit, AbilityIds.Fireball, true, true);
        Place(r);
        game.SetUnitColor(r.Unit, Vector3.One);
    }

    private Racer? Director() => racers.Find(r => !r.Computer && !r.Withdrawn);

    private void SetGarageControls(Racer r, bool open, bool director)
    {
        if (!r.Computer) game.GetPlayer(r.Seat).SetHudElementVisible(HudElement.ResourceBar, true);
        foreach (var part in Workshop) game.SetAbilityState(r.Unit, part.Ability, !open, !open);
        game.SetAbilityState(r.Unit, PickCar, !open, !open);
        game.SetAbilityState(r.Unit, PickLaps, !open || !director, !open || !director);
        game.SetAbilityState(r.Unit, StartRace, !open || !director, !open || !director);
        game.SetAbilityState(r.Unit, AbilityIds.TurboBoost, open, open);
        game.SetAbilityState(r.Unit, AbilityIds.SteerLeft, open, open);
        game.SetAbilityState(r.Unit, AbilityIds.SteerRight, open, open);
        game.SetAbilityState(r.Unit, CrystalAbility, true, open);
        if (open)
            game.SetAbilityState(r.Unit, RepairAbility, true, true);
        else RefreshRepair(r);
    }

    private void RefreshGarage()
    {
        var director = Director();
        if (director == null) { OpenRace(); return; }
        game.SetLeaderboardVisible("Garage", true);
        game.SetLeaderboardValue("Laps [Z]", $"{Laps}   ·   1 / 2 / 3 / 5");
        game.SetLeaderboardValue("Start [C]", director.Name);
        foreach (var r in racers)
        {
            if (!r.Withdrawn && !r.Computer)
            {
                SetGarageControls(r, true, r == director);
                BindDriver(r);
            }
            ShowGarageLoadout(r);
        }
    }

    private void ShowGarageLoadout(Racer r) =>
        game.SetLeaderboardValue($"P{r.Seat} · {r.Name} [X]", r.Withdrawn ? "Retired" :
            $"{r.Profile.Name} · {r.Installed.Name}   STR {r.Profile.Strength}  AGI {r.Profile.Agility}  ARM {r.Profile.Armor}");

    private void FitPart(Racer r, Part selected)
    {
        r.Installed = r.Installed == selected ? Stock : selected;
        ShowGarageLoadout(r);
    }

    private void GarageAction(Racer r, string ability)
    {
        if (r.Computer || r.Withdrawn) return;
        r.GarageInputReceived = true;
        foreach (var part in Workshop)
            if (part.Ability == ability) { FitPart(r, part); return; }
        if (ability == PickCar)
        {
            int next = (r.Car + 1) % Cars.Length;
            var pos = Sample(r.Distance, r.Offset, out _);
            var replacement = game.SpawnUnitForPlayer(Cars[next], pos, r.Seat, false, true);
            if (!replacement.IsValid) return;
            var previous = r.Unit;
            r.Unit = replacement;
            r.GarageInputReceived = false;
            r.Car = next;
            r.DriveAnimation = "";
            ConfigureCar(r);
            SetGarageControls(r, true, r == Director());
            game.DestroyUnit(previous, false, false);
            BindDriver(r);
            ShowGarageLoadout(r);
        }
        else if (r == Director() && ability == PickLaps)
        {
            lapOption = (lapOption + 1) % LapOptions.Length;
            game.SetLeaderboardValue("Laps [Z]", $"{Laps}   ·   1 / 2 / 3 / 5");
        }
        else if (r == Director() && ability == StartRace) OpenRace();
    }

    private void OpenRace()
    {
        garage = false;
        clock = -5;
        game.ClearLeaderboard();
        foreach (var r in racers)
        {
            if (r.Withdrawn) continue;
            game.SetPlayerGold(r.Seat, r.Coins);
            SetGarageControls(r, false, false);
            if (!r.Computer) BindDriver(r);
        }
        game.SetLeaderboardVisible("Ember Circuit", true);
        PublishBoard();
    }

    private void BindDriver(Racer r)
    {
        game.GetPlayer(r.Seat).SelectUnit(r.Unit);
        game.SetPlayerCameraFollowUnit(r.Seat, r.Unit, garage ? 5 : 10, garage ? 2.4f : 4.6f,
            garage ? -18 : -26, garage ? 130 : 0, true, 7, true);
    }

    private void Place(Racer r)
    {
        Vector2 p = Sample(r.Distance + r.Runout, r.Offset, out var dir);
        float height = r.Flying ? r.FlightHeight : game.GetTerrainHeight(p.X, p.Y);
        r.WorldPosition = new(p.X, height, p.Y);
        game.TeleportUnit(r.Unit, r.WorldPosition);
        game.SetUnitFacing(r.Unit, r.Computer || float.IsFinite(r.Finish) ? MathF.Atan2(dir.X, dir.Y) : r.Heading);
        string animation;
        if (r.FrozenUntil > clock) animation = "Idle";
        else if (r.Flying)
            animation = r.FlightTime < (r.OnLaunchPad ? 8.2f : 1.5f) / 22 ? "Climb" : "Descend";
        else if (r.Speed < 0.6f || float.IsFinite(r.Finish))
            animation = "Idle";
        else
        {
            Vector2 front = p + dir;
            Vector2 rear = p - dir;
            float rise = game.GetTerrainHeight(front.X, front.Y) - game.GetTerrainHeight(rear.X, rear.Y);
            Sample(r.Distance + 1, 0, out var next);
            float turn = r.Computer ? r.Speed * (dir.Y * next.X - dir.X * next.Y) : r.YawRate;
            animation = rise > 0.32f ? "Climb" : rise < -0.32f ? "Descend" :
                turn > 0.32f ? "LeanLeft" : turn < -0.32f ? "LeanRight" :
                r.Boost > 0 || r.OnLaunchPad ? "Surge" : "Drive";
        }
        if (animation != r.DriveAnimation)
        {
            r.DriveAnimation = animation;
            game.SetUnitAnimation(r.Unit, "Loop:" + animation);
        }
    }

    private void OnAbility(UnitId unit, string ability, Vector3 target)
    {
        if (ended || podiumUntil > 0) return;
        foreach (var r in racers)
        {
            if (r.Unit != unit || float.IsFinite(r.Finish)) continue;
            if (garage) { GarageAction(r, ability); return; }
            if (ability == AbilityIds.SteerLeft) r.LeftHeld = true;
            if (ability == AbilityIds.SteerRight) r.RightHeld = true;
            if (ability == AbilityIds.SteerLeftStop) r.LeftHeld = false;
            if (ability == AbilityIds.SteerRightStop) r.RightHeld = false;
            if (clock < 0)
            {
                if (ability == AbilityIds.TurboBoost && !r.LaunchAttempted)
                {
                    r.LaunchAttempted = true;
                    r.LaunchReady = clock >= -0.65f;
                    Notify(r, r.LaunchReady ? "Launch primed!" : "Too early", r.LaunchReady ? Cyan : Amber);
                }
                return;
            }
            if (ability == AbilityIds.TurboBoost) Boost(r);
            if (ability == AbilityIds.Fireball) ChooseTarget(r);
            if (ability == CrystalAbility) UsePower(r);
            if (ability == RepairAbility) Repair(r);
            break;
        }
    }

    private void Boost(Racer r)
    {
        if (!r.Charged || r.Boost > 0 || r.JamUntil > clock || r.FrozenUntil > clock) return;
        r.Charged = false;
        game.SetAbilityState(r.Unit, AbilityIds.TurboBoost, true, false);
        r.Boost = 2;
        game.SpawnExpandingGroundRing(r.Unit.Position, 1, 5, 0.3f, Cyan);
    }

    private void Notify(Racer r, string key, Vector3 color)
    {
        if (!r.Computer) game.ShowPlayerFeedbackText(r.Seat, game.Translate(key, r.Seat), color);
    }

    private void PlaceRacePickups()
    {
        AddCrystalRow(10);
        for (int i = 3; i < waypoints.Count; i += 6)
            AddCrystalRow(waypoints[i]);

        // Named waypoint numbers at bend apexes, away from launch pads and cliff edges.
        int[] coinBends = { 3, 7, 9, 12, 15, 18, 21, 26, 30, 32, 36, 38, 43, 48 };
        for (int i = 0; i < coinBends.Length; i++)
        {
            int index = coinBends[i] - 1;
            if (index >= waypoints.Count) continue;
            float apex = waypoints[index];
            Sample(apex - 6, 0, out var entry);
            Sample(apex + 6, 0, out var exit);
            int inside = Math.Sign(entry.X * exit.Y - entry.Y * exit.X);
            if (inside == 0) continue;
            bool dirt = i % 2 == 1;
            float edge = dirt ? RoadEdge + 2.5f : RoadEdge - 1;
            int side = dirt ? -inside : inside;
            for (int j = -1; j <= 1; j++)
                AddPickup(apex + 5 * j, side * (edge - Math.Abs(j) * 0.4f), true);
        }
    }

    private void AddCrystalRow(float distance)
    {
        const int crystalsPerRow = 5;
        float spacing = 2 * RoadEdge / crystalsPerRow;
        for (int i = 0; i < crystalsPerRow; i++)
            AddPickup(distance, (i + 0.5f) * spacing - RoadEdge);
    }

    private void AddPickup(float distance, float offset, bool coin = false)
    {
        var p = Sample(distance, offset, out var forward);
        var pickup = new Pickup {
            Position = new(p.X, game.GetTerrainHeight(p.X, p.Y), p.Y),
            IsCoin = coin, Facing = MathF.Atan2(forward.X, forward.Y)
        };
        SpawnPickup(pickup);
        pickups.Add(pickup);
    }

    private void SpawnPickup(Pickup c)
    {
        string template = c.IsCoin ? "unit/race_coin" : UnitIds.Kevin;
        c.Model = game.SpawnUnitForPlayer(template, new Vector2(c.Position.X, c.Position.Z), 0, false, true);
        if (c.Model.IsValid)
        {
            if (c.IsCoin) game.SetUnitFacing(c.Model, c.Facing);
            c.Model.Invulnerable = true;
            c.Model.HideHealthAndManaBars = true;
            game.SetUnitCommandsFrozen(c.Model, true);
        }
    }

    private static bool Racing(Racer r) => !r.Withdrawn && !float.IsFinite(r.Finish);
    private static bool Directed(Power p) => p == Power.FrostBolt || p == Power.Disruptor;

    private void UpdatePickups()
    {
        if (clock < nextPickupCheck) return;
        nextPickupCheck = clock + 0.06f;
        foreach (var c in pickups)
        {
            if (!c.Model.IsValid)
            {
                if (clock >= c.RespawnAt) SpawnPickup(c);
                continue;
            }
            Racer? winner = null;
            float closest = 4;
            foreach (var r in racers)
            {
                if (!Racing(r) || r.Flying || (!c.IsCoin && r.StoredPower != Power.None)) continue;
                float distance = Vector3.DistanceSquared(r.WorldPosition, c.Position);
                if (distance < closest || (winner != null && distance == closest && r.Seat < winner.Seat))
                {
                    closest = distance;
                    winner = r;
                }
            }
            if (winner == null) continue;
            game.DestroyUnit(c.Model, false, false);
            c.Model = UnitId.Invalid;
            c.RespawnAt = clock + 7;
            if (c.IsCoin)
            {
                winner.Coins++;
                game.SetPlayerGold(winner.Seat, winner.Coins);
                RefreshRepair(winner);
            }
            else CollectPower(winner, c.Position);
        }
        for (int i = mines.Count - 1; i >= 0; i--)
        {
            var mine = mines[i];
            var victim = clock < mine.Expires ? racers.Find(r => r.Seat != mine.Owner && Racing(r) && !r.Flying &&
                Vector3.DistanceSquared(r.WorldPosition, mine.Position) <= 4) : null;
            if (victim == null && clock < mine.Expires) continue;
            if (victim != null) Hit(victim, Power.Mine);
            game.DestroyStaticText(mine.Sign);
            mines.RemoveAt(i);
        }
    }

    private static string PowerName(Power power) => power switch
    {
        Power.Grip => "Rally tyres", Power.Shield => "Ember shield",
        Power.FrostBolt => "Frost bolt", Power.Disruptor => "Disruptor dart",
        Power.Shockwave => "Shockwave", Power.Blackout => "Blackout", Power.Mine => "Ember mines", Power.Winterlock => "Winterlock", _ => ""
    };

    private Power RollPower(Racer r)
    {
        int rivals = 0, ahead = 0;
        foreach (var other in racers)
        {
            if (other == r || !Racing(other)) continue;
            rivals++;
            if (other.Distance > r.Distance || (other.Distance == r.Distance && other.Seat < r.Seat)) ahead++;
        }
        if (rivals == 0) return game.RandomInt(0, 1) == 0 ? Power.Grip : Power.Shield;
        int roll = game.RandomInt(1, 100 * rivals);
        foreach (var odds in CrystalOdds)
        {
            roll -= odds.First * (rivals - ahead) + odds.Last * ahead;
            if (roll <= 0) return odds.Item;
        }
        throw new InvalidOperationException("Crystal odds must total 100 at each end of the field.");
    }

    private void CollectPower(Racer r, Vector3 position)
    {
        r.StoredPower = RollPower(r);
        r.Charges = r.StoredPower == Power.Mine ? MineCharges : 1;
        r.Target = null;
        game.SetAbilityState(r.Unit, CrystalAbility, false, false);
        game.SetAbilityState(r.Unit, AbilityIds.Fireball, !Directed(r.StoredPower), !Directed(r.StoredPower));
        game.SetUnitMana(r.Unit, 100);
        string name = game.Translate(PowerName(r.StoredPower), r.Seat);
        if (r.StoredPower == Power.Mine) name += " ×" + r.Charges;
        game.CreateFloatingText(name, position, Cyan, 2);
        game.SpawnExpandingGroundRing(position, 0.4f, 2, 0.3f, Cyan);
        if (r.Computer) return;
        string message = name + "  " + (Directed(r.StoredPower) ? game.Translate("F: choose rival; E: fire", r.Seat) : "[E]");
        game.ShowPlayerFeedbackText(r.Seat, message, Cyan);
        game.GetPlayer(r.Seat).SendMessage(message);
    }

    private void ChooseTarget(Racer r)
    {
        if (!Directed(r.StoredPower)) return;
        int seat = r.Target?.Seat ?? r.Seat;
        for (int step = 1; step <= 8; step++)
        {
            int next = (seat - 1 + step) % 8 + 1;
            var target = racers.Find(o => o.Seat == next && o != r && Racing(o));
            if (target == null) continue;
            r.Target = target;
            if (!r.Computer) game.ShowPlayerFeedbackText(r.Seat, "[E] → " + target.Name, Amber);
            return;
        }
        r.Target = null;
    }

    private void Hit(Racer victim, Power power)
    {
        game.SpawnExpandingGroundRing(victim.WorldPosition, 0.5f, 3, 0.35f, Amber);
        if (victim.ShieldUntil > clock) { Notify(victim, "Ember shield", Cyan); return; }
        if (power == Power.Winterlock)
        {
            victim.FrozenUntil = clock + FreezeSeconds;
            victim.Boost = 0;
            Place(victim);
        }
        else if (power == Power.Disruptor || power == Power.Blackout)
        {
            victim.Boost = 0;
            victim.JamUntil = Math.Max(victim.JamUntil, clock + (power == Power.Disruptor ? 5 : 2.5f));
        }
        else
        {
            float duration = power == Power.Mine ? 5 : (power == Power.FrostBolt ? 1.6f : 0.8f) * victim.ImpactTime;
            victim.Drag = Math.Max(victim.Drag, duration);
            victim.Boost = 0;
        }
        Notify(victim, PowerName(power), Amber);
    }

    private void DamageChassis(Racer r, int amount)
    {
        r.Integrity = Math.Max(0, r.Integrity - amount);
        // Zero native HP destroys the unit. Keep it alive with a fraction that displays as zero.
        game.SetUnitHealth(r.Unit, Math.Max(0.001f, r.Integrity));
        RefreshRepair(r);
    }

    private void RefreshRepair(Racer r) =>
        game.SetAbilityState(r.Unit, RepairAbility, r.Coins < RepairCost || r.Integrity == 100, false);

    private void Repair(Racer r)
    {
        if (!Racing(r) || clock <= 0 || r.Coins < RepairCost || r.Integrity == 100) return;
        r.Coins -= RepairCost;
        r.Integrity = Math.Min(100, r.Integrity + 10);
        game.SetPlayerGold(r.Seat, r.Coins);
        game.SetUnitHealth(r.Unit, r.Integrity);
        RefreshRepair(r);
        Notify(r, "Chassis repaired", Cyan);
    }

    private void UsePower(Racer r)
    {
        var power = r.StoredPower;
        if (power == Power.None || r.Flying || r.FrozenUntil > clock) return;
        if (power == Power.Winterlock && clock < nextWinterlock)
        {
            if (!r.Computer) Notify(r, "Winterlock recharging", Cyan);
            return;
        }
        if (Directed(power))
        {
            if (r.Computer && (r.Target == null || !Racing(r.Target))) ChooseTarget(r);
            if (r.Target != null && Racing(r.Target))
            {
                var from = r.WorldPosition + Vector3.UnitY;
                var to = r.Target.WorldPosition + Vector3.UnitY;
                if (power == Power.Disruptor)
                    game.SpawnProjectile("arrow", from, to, Math.Max(50, Vector3.Distance(from, to) * 8));
                else
                    game.SpawnChainBeam("lightning", new[] { from, to }, 0.4f, 1, 0.1f, 0.08f, Cyan);
                Hit(r.Target, power);
            }
            else if (racers.Exists(o => o != r && Racing(o)))
            {
                Notify(r, "Choose a rival with F", Amber);
                return;
            }
        }
        else if (power == Power.Grip) r.GripUntil = clock + 4;
        else if (power == Power.Shield)
        {
            r.Drag = 0;
            r.JamUntil = 0;
            r.ShieldUntil = clock + 6;
        }
        else if (power == Power.Mine)
        {
            if (r.Computer && clock < r.NextBotMine) return;
            r.NextBotMine = clock + 1.25f;
            Vector2 p = Sample(r.Distance - 1.8f, r.Offset, out _);
            Vector3 position = new(p.X, game.GetTerrainHeight(p.X, p.Y), p.Y);
            int sign = game.CreateStaticText("✹", position + 0.4f * Vector3.UnitY, Amber, 180);
            mines.Add(new(position, r.Seat, clock + 14, sign));
        }
        else
        {
            if (power == Power.Winterlock) nextWinterlock = clock + FreezeSeconds + 3;
            foreach (var other in racers)
                if (other != r && Racing(other)) Hit(other, power);
        }
        Notify(r, PowerName(power), Cyan);
        r.Charges--;
        game.SetUnitMana(r.Unit, power == Power.Mine ? 100 * r.Charges / MineCharges : 0);
        if (r.Charges > 0) return;
        r.StoredPower = Power.None;
        r.Target = null;
        game.SetAbilityState(r.Unit, CrystalAbility, true, false);
        game.SetAbilityState(r.Unit, AbilityIds.Fireball, true, true);
    }

    private void Recharge(Racer r, string message)
    {
        if (r.Charged) return;
        r.Charged = true;
        r.Draft = 0;
        game.SetAbilityState(r.Unit, AbilityIds.TurboBoost, false, false);
        Notify(r, message, Cyan);
        if (!r.Computer) game.PlayPlayerClickSound(r.Seat);
    }

    public void Update(IGameAPI api, float delta)
    {
        if (ended || delta <= 0) return;
        if (garage)
        {
            garageTime += delta;
            if (garageTime >= 1)
            {
                garageTime = 0;
                foreach (var r in racers)
                    if (!r.Computer && !r.Withdrawn && !r.GarageInputReceived)
                        BindDriver(r);
            }
            return;
        }
        float previous = clock;
        clock += delta;
        if (clock <= 0)
        {
            int digit = (int)MathF.Ceiling(-clock);
            if (digit >= 1 && digit <= 5 && digit != countdownDigit)
            {
                countdownDigit = digit;
                if (startSign == 0)
                {
                    Vector2 line = Sample(3, 0, out _);
                    startSign = game.CreateStaticText(digit.ToString(), new(line.X, game.GetTerrainHeight(line.X, line.Y), line.Y), Amber, 260);
                }
                else game.SetStaticText(startSign, digit.ToString());
                game.StartCountdownTimer(-clock, "Race Start");
                foreach (var r in racers)
                    if (!r.Withdrawn && !r.Computer)
                    {
                        if (digit == 5) BindDriver(r);
                        game.ShowPlayerFeedbackText(r.Seat, digit.ToString(), Amber);
                    }
            }
            return;
        }
        if (podiumUntil > 0)
        {
            foreach (var r in racers)
                if (!r.Withdrawn) Park(r, delta);
            if (clock >= podiumUntil)
            {
                ended = true;
                game.TriggerPlayerVictory(racers[0].Seat);
            }
            return;
        }
        if (previous <= 0)
        {
            game.StopCountdownTimer();
            if (startSign != 0) game.DestroyStaticText(startSign);
            foreach (var r in racers)
            {
                if (!r.Withdrawn && !r.Computer) BindDriver(r);
                if (r.LaunchReady || (r.Computer && game.RandomFloat(0, 1) < 0.35f))
                    r.Speed = CruiseSpeed;
                Notify(r, "Go!", Cyan);
            }
        }
        delta = Math.Min(clock, delta);
        UpdatePickups();
        // Snapshot all gaps before moving anyone, so changing the standings cannot change traffic.
        foreach (var r in racers)
        {
            r.FrameDistance = r.Distance;
            r.FrameOffset = r.Offset;
            r.FrameSpeed = r.FrozenUntil > clock ? 0 : r.Speed;
            r.FrameFinished = float.IsFinite(r.Finish) || r.Withdrawn;
        }
        foreach (var r in racers)
        {
            r.Gap = LaneGap(r, r.Offset, out r.Ahead);
        }
        foreach (var r in racers)
        {
            if (r.Withdrawn) continue;
            if (float.IsFinite(r.Finish)) Park(r, delta);
            else Advance(r, delta);
        }

        if (clock >= nextBoard)
        {
            nextBoard = clock + 0.4f;
            PublishBoard();
        }
        if (!racers.TrueForAll(r => r.Withdrawn || float.IsFinite(r.Finish))) return;
        if (!racers.Exists(r => float.IsFinite(r.Finish))) { ended = true; return; }
        podiumUntil = clock + 5;
        PublishBoard();
        game.SetSummaryTableHeaders("Place", "Driver", "Time", "Best Lap");
        for (int i = 0; i < racers.Count; i++)
            game.SetSummaryTableRow($"{i+1}", racers[i].Name, racers[i].Withdrawn ? "Retired" : RaceTime(racers[i].Finish),
                float.IsFinite(racers[i].BestLap) ? RaceTime(racers[i].BestLap) : "—");
        game.ShowSummaryTable("Ember Circuit", true);
    }

    private void Park(Racer r, float dt)
    {
        // Pull clear of the finish line, leaving room for the following racers.
        float stall = 2 + 1.6f * ((r.Seat - 1) / 2);
        float side = (RoadEdge + 1.4f) * (r.Seat % 2 == 0 ? 1 : -1);
        if (r.Runout >= stall && r.Offset == side) return;
        r.Runout = Math.Min(stall, r.Runout + 3 * dt);
        r.Offset += Math.Clamp(side - r.Offset, -2 * dt, 2 * dt);
        Place(r);
    }

    private float LaneGap(Racer r, float offset, out Racer? ahead)
    {
        ahead = null;
        float nearest = float.PositiveInfinity;
        foreach (var other in racers)
        {
            if (other == r || other.FrameFinished || Math.Abs(other.FrameOffset - offset) > 1.05f) continue;
            float gap = (other.FrameDistance - r.FrameDistance) % Length;
            if (gap < 0) gap += Length;
            if (gap == 0 && other.Seat > r.Seat) continue;
            if (gap >= nearest) continue;
            nearest = gap;
            ahead = other;
        }
        return nearest;
    }

    private void DriveComputer(Racer r, Gate gate, float toGate, float dt)
    {
        r.DecisionDelay -= dt;
        if (toGate < GateLookAhead && r.PlannedGate != r.NextGate)
        {
            r.PlannedGate = r.NextGate;
            // The three lane indices sum to zero.
            int safe = -gate.Lane - HazardLane(gate);
            r.Lane = !r.Charged || game.RandomFloat(0, 1) < 0.55f ? gate.Lane : safe;
        }
        // Stay in the wake until charged, then look for space on either side.
        if (r.Charged && r.Gap < 3.8f && toGate > 4 && r.DecisionDelay <= 0 &&
            Math.Abs(r.Offset - r.Lane * LaneWidth) < 0.25f)
        {
            int best = r.Lane;
            float room = r.Gap;
            for (int lane = -1; lane <= 1; lane++)
            {
                if (Math.Abs(lane - r.Lane) != 1 || (toGate < GateLookAhead && lane == HazardLane(gate))) continue;
                float opening = LaneGap(r, lane * LaneWidth, out _);
                if (opening > room + 1) { best = lane; room = opening; }
            }
            r.Lane = best;
            r.DecisionDelay = 1.0f;
        }
        if (r.Charged && r.Gap > 4 && r.Drag <= 0 &&
            (toGate < GateLookAhead || r.Distance > Laps * Length - CruiseSpeed || r.DecisionDelay > 0))
            Boost(r);
    }

    private static string RaceTime(float seconds)
    {
        int ticks = (int)MathF.Round(seconds * 100);
        return $"{ticks / 6000}:{ticks / 100 % 60:00}.{ticks % 100:00}";
    }

    private void Advance(Racer r, float dt)
    {
        if (r.FrozenUntil > clock || r.Flying)
            r.Drag = Math.Max(0, r.Drag - dt);
        if (r.FrozenUntil > clock) return;
        if (r.Computer) UsePower(r);
        if (r.Flying)
        {
            Fly(r, dt);
            return;
        }
        int lap = r.CompletedLaps;
        if (gates.Count > 0)
        {
            Gate gate = gates[r.NextGate % gates.Count];
            float toGate = (r.NextGate / gates.Count) * Length + gate.Distance - r.Distance;
            if (r.Computer) DriveComputer(r, gate, toGate, dt);
            else if (toGate < GateLookAhead && r.AnnouncedGate != r.NextGate)
            {
                r.AnnouncedGate = r.NextGate;
                Notify(r, gate.Lane switch { -1 => "Recharge: left", 0 => "Recharge: centre", _ => "Recharge: right" }, Cyan);
            }
        }

        bool drafting = r.Gap <= 6f && r.Speed > 3 && r.Distance > 0 && r.Drag <= 0 && r.Boost <= 0;
        if (!r.Charged)
        {
            r.Draft = drafting ? r.Draft + dt : Math.Max(0, r.Draft - 2 * dt);
            if (r.Draft >= DraftSeconds) Recharge(r, "Slipstream charged! Change lane and boost.");
        }
        float dirt = Math.Clamp((Math.Abs(r.Offset) - RoadEdge) / 0.8f, 0, 1);
        bool boosting = r.Boost > 0;
        float targetSpeed = r.Drag > 0 ? 3.8f : boosting ? BoostSpeed : drafting ? CruiseSpeed + 0.65f : CruiseSpeed;
        if (r.LeftHeld && r.RightHeld) targetSpeed = Math.Min(4.5f, targetSpeed);
        if (r.ShieldUntil <= clock) targetSpeed *= 1 - (r.Installed == Suspension ? 0.40f : 0.48f) * dirt;
        // Tyres scrubbing sideways bleed speed. A straight exit preserves momentum.
        float slip = MathF.IEEERemainder(r.Heading - r.TravelHeading, MathF.Tau);
        targetSpeed *= 1 - 0.16f * MathF.Sin(slip) * MathF.Sin(slip);
        float deceleration = r.LeftHeld && r.RightHeld ? 27 : 15;
        float acceleration = (boosting ? 22 : 13) * r.AccelerationScale;
        targetSpeed *= r.EngineSpeedScale;
        r.Speed += Math.Clamp(targetSpeed - r.Speed, -deceleration * dt, acceleration * dt);
        if (r.Ahead != null && r.Gap < BumperSpacing + Math.Max(0.6f, (r.Speed - r.Ahead.FrameSpeed) * dt))
        {
            float clearance = Math.Max(0, r.Gap - BumperSpacing);
            r.Speed = Math.Min(r.Speed, r.Ahead.FrameSpeed + clearance * 2);
        }
        r.Boost = Math.Max(0, r.Boost - dt);
        r.Drag = Math.Max(0, r.Drag - dt);
        float previousDistance = r.Distance;
        if (r.Computer)
        {
            foreach (float lip in jumpLips)
            {
                float ahead = (lip - r.Distance) % Length;
                if (ahead < 0) ahead += Length;
                if (ahead < 9 + Math.Max(CruiseSpeed, r.Speed) * 1.25f) r.Lane = 0;
            }
            r.Offset += Math.Clamp(r.Lane * LaneWidth - r.Offset, -5*dt, 5*dt);
            r.Distance += r.Speed * dt;
        }
        else
            Steer(r, dt, dirt, boosting, slip);
        float progress = r.Distance - previousDistance;
        float lapBase = MathF.Floor(r.Distance / Length) * Length;
        foreach (float point in waypoints)
            if (previousDistance < lapBase + point && r.Distance >= lapBase + point)
                r.Checkpoint = lapBase + point;
        foreach (var edge in cliffEdges)
        {
            float along = r.Distance - lapBase - edge.Start;
            if (along < 0 || along > 26 || r.Offset * edge.Side < RoadEdge + 1.75f) continue;
            var rim = Sample(r.Distance, edge.Side * RoadEdge, out _);
            r.OnLaunchPad = false;
            r.Flying = true;
            r.FlightTime = 0;
            r.TakeoffHeight = r.FlightHeight = game.GetTerrainHeight(rim.X, rim.Y);
            r.AirForward = progress / dt;
            r.AirSide = edge.Side * 3;
            Place(r);
            return;
        }
        foreach (float localLip in jumpLips)
        {
            float lip = lapBase + localLip;
            if (r.Distance < lip - 8) continue;
            if (r.Distance < lip && !r.OnLaunchPad && progress > 0 && Math.Abs(r.Offset) <= LaneWidth / 2 - 0.1f)
            {
                r.OnLaunchPad = true;
                r.Speed = Math.Max(LaunchSpeed * r.EngineSpeedScale, r.Speed);
                game.SpawnExpandingGroundRing(r.Unit.Position, 0.4f, 2, 0.3f, Cyan);
            }
            if (r.OnLaunchPad && r.Distance < lip && (Math.Abs(r.Offset) > LaneWidth / 2 || progress <= 0))
                r.OnLaunchPad = false;
            if (r.Distance >= lip && r.Distance < lip + GapWidth)
            {
                bool forward = previousDistance < lip;
                r.OnLaunchPad &= forward;
                r.JumpLip = lip;
                r.FlightTime = 0;
                var edge = Sample(forward ? lip - 2 : lip + GapWidth + 2, r.Offset, out var tangent);
                r.TakeoffHeight = r.FlightHeight = game.GetTerrainHeight(edge.X, edge.Y);
                float angle = r.Computer ? 0 : r.TravelHeading - MathF.Atan2(tangent.X, tangent.Y);
                r.AirForward = forward ? Math.Max(0, MathF.Cos(angle)) * (r.OnLaunchPad ? Math.Max(16f, r.Speed) : r.Speed) : 0;
                r.AirSide = -MathF.Sin(angle) * r.Speed;
                r.Flying = true;
                break;
            }
        }
        if (gates.Count > 0)
        {
            Gate gate = gates[r.NextGate % gates.Count];
            float center = (r.NextGate / gates.Count) * Length + gate.Distance;
            if (previousDistance > center + 3.7f)
                r.NextGate++;
            else if (progress > 0 && !r.Flying && r.Distance >= center - 3.7f)
            {
                if (Math.Abs(r.Offset - gate.Lane * LaneWidth) <= 1.65f)
                {
                    Recharge(r, "Boost ready [Q]");
                    r.Speed = Math.Max(r.Speed, (CruiseSpeed + 4) * r.EngineSpeedScale);
                    game.SpawnExpandingGroundRing(r.Unit.Position, 0.4f, 2, 0.3f, Cyan);
                    r.NextGate++;
                }
                else if (Math.Abs(r.Offset - HazardLane(gate) * LaneWidth) <= 1.65f)
                {
                    r.NextGate++;
                    if (r.ShieldUntil <= clock)
                    {
                        r.Drag = Math.Max(r.Drag, 1.4f);
                        r.Boost = 0;
                        r.Draft = 0;
                        Notify(r, "Hot coals", Amber);
                    }
                }
            }
        }
        if (!r.StartedLap && previousDistance < 0 && r.Distance >= 0)
        {
            r.LapStart = clock - dt * r.Distance / progress;
            r.StartedLap = true;
        }
        if (previousDistance < (lap + 1) * Length && r.Distance >= (lap + 1) * Length)
        {
            r.CompletedLaps++;
            float crossing = clock - dt * (r.Distance - (lap + 1) * Length) / progress;
            float split = crossing - r.LapStart;
            r.BestLap = Math.Min(r.BestLap, split);
            r.LapStart = crossing;
            if (lap + 1 == Laps)
            {
                r.Finish = crossing;
                r.Distance = Laps * Length;
                Notify(r, "Finished!", Cyan);
                game.SpawnExpandingGroundRing(r.Unit.Position, 0.5f, 3, 0.5f, Cyan);
            }
            else if (!r.Computer)
            {
                string key = lap + 2 == Laps ? "Final lap!   {0}" : "Lap {1}/{2}   {0}";
                game.ShowPlayerFeedbackText(r.Seat,
                    string.Format(game.Translate(key, r.Seat), RaceTime(split), lap + 2, Laps), Cyan);
            }
        }
        Place(r);
    }

    private void Fly(Racer r, float dt)
    {
        r.FlightTime += dt;
        r.Distance += r.AirForward * dt;
        r.Offset = Math.Clamp(r.Offset + r.AirSide * dt, -ShoulderEdge, ShoulderEdge);
        float lift = r.OnLaunchPad ? 8.2f : 1.5f;
        r.FlightHeight = r.TakeoffHeight + r.FlightTime * (lift - 11 * r.FlightTime);
        r.Boost = Math.Max(0, r.Boost - dt);
        if (r.OnLaunchPad && r.Distance >= r.JumpLip + GapWidth && r.FlightTime > lift / 22)
        {
            Vector2 landing = Sample(r.Distance, r.Offset, out _);
            float ground = game.GetTerrainHeight(landing.X, landing.Y);
            if (r.FlightHeight >= ground - 0.6f && r.FlightHeight <= ground + 0.5f)
            {
                r.Flying = r.OnLaunchPad = false;
                r.LandingSlip = Math.Clamp(Math.Abs(r.AirSide) / 9, 0, 0.65f);
                float lapBase = MathF.Floor(r.Distance / Length) * Length;
                foreach (float point in waypoints)
                    if (lapBase + point <= r.Distance && lapBase + point > r.Checkpoint)
                        r.Checkpoint = lapBase + point;
            }
        }
        if (r.Flying && r.FlightHeight < r.TakeoffHeight - 1)
        {
            r.AirForward = r.AirSide = 0;
            if (r.FlightHeight < r.TakeoffHeight - 9)
            {
                r.Distance = r.Checkpoint;
                r.Offset = 0;
                Sample(r.Distance, 0, out var facing);
                r.Heading = r.TravelHeading = MathF.Atan2(facing.X, facing.Y);
                r.Speed = r.YawRate = r.Boost = r.Drag = r.Draft = 0;
                r.Steering = r.RearSlip = r.LandingSlip = 0;
                r.OnLaunchPad = r.Flying = false;
                DamageChassis(r, 25);
                Notify(r, "Waypoint", Amber);
            }
        }
        Place(r);
    }

    private void Steer(Racer r, float dt, float dirt, bool boosting, float slip)
    {
        int turn = (r.LeftHeld ? 1 : 0) - (r.RightHeld ? 1 : 0);
        bool braking = r.LeftHeld && r.RightHeld;
        // Braking in a turn keeps the wheels angled briefly while weight moves forward.
        float steeringRate = braking ? 2.5f : turn == 0 ? 7f : 8.5f;
        if (r.Installed == Suspension && turn != 0) steeringRate /= 1 + 0.10f * (1 - dirt);
        r.Steering += Math.Clamp(turn - r.Steering, -steeringRate * dt, steeringRate * dt);
        float roadGrip = (1 - 0.32f * dirt) * (clock < r.GripUntil ? 1.65f : 1);
        float lateralLoad = Math.Abs(r.YawRate) * r.Speed / ((boosting ? 18 : 31) * roadGrip);
        float breakaway = Math.Clamp((lateralLoad - (braking ? 0.5f : 0.85f)) * 0.95f, 0, 1);
        bool correcting = turn * slip < -0.08f;
        float gripResponse = breakaway > r.RearSlip ? 4.5f : correcting ? 4 : 1.6f;
        if (correcting && breakaway < r.RearSlip) gripResponse /= r.RecoveryTime;
        r.RearSlip += (breakaway - r.RearSlip) * (1 - MathF.Exp(-gripResponse * dt));
        float settlingTime = (1 - 0.10f * (r.Profile.Armor - 3)) * (r.Installed == Suspension ? 0.85f : 1);
        r.LandingSlip = Math.Max(0, r.LandingSlip - dt / settlingTime);
        float effectiveSlip = Math.Max(r.RearSlip, r.LandingSlip);
        float steeringAuthority = Math.Clamp(r.Speed / 3, 0, 1);
        float slideYaw = Math.Clamp(slip, -0.9f, 0.9f) * effectiveSlip * (braking ? 1.2f : 0.7f);
        float yawDemand = steeringAuthority * (r.Steering * (boosting ? 3f : 2.65f) /
            (1 + Math.Abs(slip) * 0.55f) + slideYaw);
        float yawResponse = boosting ? 4.2f : 7.5f;
        r.YawRate += (yawDemand - r.YawRate) * (1 - MathF.Exp(-yawResponse * dt));
        r.Heading = MathF.IEEERemainder(r.Heading + r.YawRate * dt, MathF.Tau);

        // Available lateral acceleration bounds how fast the velocity vector can turn.
        // Under boost more of the tyre grip is spent accelerating; loose dirt also reduces grip.
        float lateralAcceleration = (boosting ? 18f : 36f) * roadGrip * (1 - 0.36f * effectiveSlip);
        float maxTurn = lateralAcceleration * dt / Math.Max(1, r.Speed);
        float headingError = MathF.IEEERemainder(r.Heading - r.TravelHeading, MathF.Tau);
        float correction = headingError * (1 - MathF.Exp(-(boosting ? 2.05f : 4.4f) * dt));
        r.TravelHeading = MathF.IEEERemainder(r.TravelHeading + Math.Clamp(correction, -maxTurn, maxTurn), MathF.Tau);
        Vector2 travel = new Vector2(MathF.Sin(r.TravelHeading), MathF.Cos(r.TravelHeading)) * (r.Speed * dt);
        // Express the driver's world-space motion in road coordinates for timing and barriers.
        // The outside of a bend takes more metres to cover than its centre line.
        Vector2 ahead = Sample(r.Distance + 0.05f, r.Offset, out _);
        Vector2 behind = Sample(r.Distance - 0.05f, r.Offset, out _);
        Vector2 along = (ahead - behind) / 0.1f;
        Sample(r.Distance, 0, out var tangent);
        Vector2 normal = new(-tangent.Y, tangent.X);
        float step = Vector2.Dot(travel, tangent) / Math.Max(0.35f, Vector2.Dot(along, tangent));
        r.Distance += step;
        r.Offset = Math.Clamp(r.Offset + Vector2.Dot(travel - along * step, normal), -ShoulderEdge, ShoulderEdge);
    }

    private void PublishBoard()
    {
        racers.Sort((a,b) => {
            if (a.Withdrawn != b.Withdrawn) return a.Withdrawn ? 1 : -1;
            int result = a.Finish.CompareTo(b.Finish);
            if (result == 0) result = b.Distance.CompareTo(a.Distance);
            return result == 0 ? a.Seat.CompareTo(b.Seat) : result;
        });
        for (int i = 0; i < racers.Count; i++)
        {
            var r = racers[i];
            string drive = r.FrozenUntil > clock ? "Frozen" : r.Boost > 0 ? "»»" : r.Charged ? "[Q]" :
                r.Draft > 0 ? $"{(int)(100*r.Draft/DraftSeconds)}%" : "—";
            string status = r.Withdrawn ? "Retired" : float.IsFinite(r.Finish) ? RaceTime(r.Finish) :
                $"{1 + r.CompletedLaps}/{Laps}   {drive}   HP {r.Integrity}   Coins {r.Coins}";
            if (r.StoredPower != Power.None) status += "   [E] " + game.Translate(PowerName(r.StoredPower), r.Seat) +
                (r.StoredPower == Power.Mine ? " ×" + r.Charges : "") +
                (r.Target == null ? "" : " → " + r.Target.Name);
            string row = $"{r.Name}   {status}";
            if (boardRows[i] == row) continue;
            boardRows[i] = row;
            game.SetLeaderboardValue($"#{i+1}", row);
        }
    }
}
