namespace Realm.Maps;

using System;
using System.Numerics;
using Realm.Ecs;
using Realm.MapAPI;

public class MapScript : IWasmModule
{
	private const int MaxRacers = 8;
	private const int TotalLaps = 3;
	private const int WaypointCount = 16;
	private const int ItemBoxCount = 8;
	private const int MaxHazards = 24;
	private const int MaxProjectiles = 16;
	private const int NeutralSlotFallback = 23;

	private const float CountdownDurationSeconds = 3.2f;
	private const float RocketBoostWindowSeconds = 0.6f;
	private const float BaseMaxSpeed = 18.0f;
	private const float TurboMaxSpeed = 38.0f;
	private const float StarMaxSpeed = 40.0f;
	private const float OffroadMaxSpeed = 10.5f;
	private const float AccelerationRate = 18.0f;
	private const float BrakeDecelerationRate = 34.0f;
	private const float CoastDecelerationRate = 6.0f;
	private const float BaseTurnRate = 2.6f;
	private const float DriftTurnRate = 3.6f;
	private const float BoostTurnRate = 1.35f;
	private const float BoostDriftTurnRate = 1.8f;
	private const float BoostTurnInertia = 7.0f;
	private const float TrackHalfWidth = 12.2f;
	private const float KartRadius = 1.15f;
	private const float LeaderboardIntervalSeconds = 0.3f;

	private enum PowerUpType
	{
		None = 0,
		TurboMushroom = 1,
		GreenShell = 2,
		RedShell = 3,
		SpikeTrap = 4,
		LightningBolt = 5,
		StarPower = 6
	}

	private struct TrackRegion
	{
		public float MinX;
		public float MinZ;
		public float MaxX;
		public float MaxZ;

		public TrackRegion(float minX, float minZ, float maxX, float maxZ)
		{
			MinX = MathF.Min(minX, maxX);
			MinZ = MathF.Min(minZ, maxZ);
			MaxX = MathF.Max(minX, maxX);
			MaxZ = MathF.Max(minZ, maxZ);
		}

		public readonly bool Contains(Vector3 pos) =>
			pos.X >= MinX && pos.X <= MaxX && pos.Z >= MinZ && pos.Z <= MaxZ;
	}

	private class RacerState
	{
		public bool Active;
		public int PlayerIndex;
		public bool IsComputer;
		public string DisplayName = string.Empty;
		public string ColoredName = string.Empty;
		public UnitId Unit = UnitId.Invalid;

		public Vector3 Position;
		public float HeadingRadians;
		public float Speed;
		public float VisualSpinOffset;
		public float CurrentTurnVelocity;

		public bool HasSteerTarget;
		public Vector3 SteerTarget;
		public float TargetHeading;
		public float KeySteerInput;

		public float BoostTimer;
		public float DriftTimer;
		public float ReverseTimer;
		public bool PendingMiniTurbo;
		public float SpinOutTimer;
		public float StarTimer;
		public float ShockedTimer;
		public float BrakeTimer;
		public float BoostPadCooldown;
		public float StarVfxCooldown;
		public float TurboVfxCooldown;
		public float RocketAttemptElapsed = -1f;

		public PowerUpType HeldItem;
		public int Lap = 1;
		public int CheckpointStage;
		public float RaceScore;
		public int Rank = 1;
		public bool Finished;
		public float FinishTime;
		public int FinishOrder;

		public int AiWaypointIndex;
		public float AiLaneOffset;
		public float AiDecisionTimer;
		public float AiTurboCooldown;
	}

	private class ItemBoxSlot
	{
		public Vector3 Position;
		public UnitId Unit = UnitId.Invalid;
		public float RespawnTimer;
	}

	private class HazardSlot
	{
		public bool Active;
		public UnitId Unit = UnitId.Invalid;
		public Vector3 Position;
		public int OwnerPlayerIndex;
		public float GraceTimer;
		public float RemainingLifetime;
	}

	private class ShellProjectileSlot
	{
		public bool Active;
		public UnitId Unit = UnitId.Invalid;
		public Vector3 Position;
		public float HeadingRadians;
		public float Speed;
		public int OwnerPlayerIndex;
		public bool IsHoming;
		public int BouncesRemaining;
		public float GraceTimer;
		public float RemainingLifetime;
	}

	private readonly RacerState[] _racers = new RacerState[MaxRacers];
	private readonly int[] _rankedIndices = new int[MaxRacers];
	private readonly ItemBoxSlot[] _itemBoxes = new ItemBoxSlot[ItemBoxCount];
	private readonly HazardSlot[] _hazards = new HazardSlot[MaxHazards];
	private readonly ShellProjectileSlot[] _projectiles = new ShellProjectileSlot[MaxProjectiles];
	private readonly Vector2[] _waypoints = new Vector2[WaypointCount];

	private IGameAPI _api = null!;
	private TrackRegion _finishRegion;
	private TrackRegion _checkpoint1Region;
	private TrackRegion _checkpoint2Region;
	private TrackRegion _checkpoint3Region;
	private TrackRegion _boostPadEastRegion;
	private TrackRegion _boostPadWestRegion;

	private int _racerCount;
	private int _neutralSlot = NeutralSlotFallback;
	private int _finishedCount;
	private float _countdownRemaining;
	private int _lastAnnouncedSecond = -1;
	private bool _raceStarted;
	private bool _raceEnded;
	private float _raceElapsed;
	private float _leaderboardRefreshTimer;
	private float _endGameTimer = -1f;
	private int _winnerRacerIndex = -1;

	public void Initialize(IGameAPI api)
	{
		_api = api;

		for (int i = 0; i < MaxRacers; i++)
		{
			_racers[i] = new RacerState();
			_rankedIndices[i] = i;
		}
		for (int i = 0; i < MaxHazards; i++) _hazards[i] = new HazardSlot();
		for (int i = 0; i < MaxProjectiles; i++) _projectiles[i] = new ShellProjectileSlot();

		InitializeTrackWaypoints();
		LoadTrackRegions();
		EnsureParticipants();
		SpawnRacers();
		SpawnItemBoxes();
		SetupInitialHudAndLeaderboard();

		_api.OnUnitOrdered += HandleUnitOrdered;
		_api.OnSpellCast += HandleSpellCast;
		_api.OnPlayerChatMessage += HandlePlayerChatMessage;
		_api.OnPlayerLeft += HandlePlayerLeft;
		_api.OnUnitSelected += HandleUnitSelected;

		_countdownRemaining = CountdownDurationSeconds;
		_lastAnnouncedSecond = 4;
		_raceStarted = false;
		_raceEnded = false;
		_raceElapsed = 0f;
	}

	public void Update(IGameAPI api, float delta)
	{
		if (delta <= 0f) return;
		if (delta > 0.1f) delta = 0.1f;

		if (!_raceStarted)
		{
			UpdateCountdown(delta);
			return;
		}

		_raceElapsed += delta;

		if (_endGameTimer > 0f)
		{
			_endGameTimer -= delta;
			if (_endGameTimer <= 0f)
			{
				FinalizeMatchOutcome();
				return;
			}
		}

		UpdateRacers(delta);
		ResolveKartCollisions();
		UpdateItemBoxes(delta);
		UpdateHazards(delta);
		UpdateProjectiles(delta);
		UpdateRankings();

		_leaderboardRefreshTimer -= delta;
		if (_leaderboardRefreshTimer <= 0f)
		{
			_leaderboardRefreshTimer = LeaderboardIntervalSeconds;
			PublishLeaderboard();
		}
	}

	private void InitializeTrackWaypoints()
	{
		_waypoints[0] = new Vector2(0f, -48f);
		_waypoints[1] = new Vector2(36f, -48f);
		_waypoints[2] = new Vector2(64f, -42f);
		_waypoints[3] = new Vector2(82f, -24f);
		_waypoints[4] = new Vector2(88f, 0f);
		_waypoints[5] = new Vector2(82f, 24f);
		_waypoints[6] = new Vector2(64f, 42f);
		_waypoints[7] = new Vector2(36f, 48f);
		_waypoints[8] = new Vector2(0f, 48f);
		_waypoints[9] = new Vector2(-36f, 48f);
		_waypoints[10] = new Vector2(-64f, 42f);
		_waypoints[11] = new Vector2(-82f, 24f);
		_waypoints[12] = new Vector2(-88f, 0f);
		_waypoints[13] = new Vector2(-82f, -24f);
		_waypoints[14] = new Vector2(-64f, -42f);
		_waypoints[15] = new Vector2(-36f, -48f);
	}

	private void LoadTrackRegions()
	{
		_finishRegion = ReadRegionOrDefault("finish_line", -3f, -61f, 3f, -35f);
		_checkpoint1Region = ReadRegionOrDefault("checkpoint_1", 74f, -6f, 102f, 6f);
		_checkpoint2Region = ReadRegionOrDefault("checkpoint_2", -4f, 35f, 4f, 61f);
		_checkpoint3Region = ReadRegionOrDefault("checkpoint_3", -102f, -6f, -74f, 6f);
		_boostPadEastRegion = ReadRegionOrDefault("boost_pad_east", 24f, -54f, 32f, -42f);
		_boostPadWestRegion = ReadRegionOrDefault("boost_pad_west", -32f, 42f, -24f, 54f);
	}

	private TrackRegion ReadRegionOrDefault(string name, float fallbackMinX, float fallbackMinZ, float fallbackMaxX, float fallbackMaxZ)
	{
		if (_api.TryGetCoordinate(name, out Vector3 min, out Vector3 max))
		{
			return new TrackRegion(min.X, min.Z, max.X, max.Z);
		}
		return new TrackRegion(fallbackMinX, fallbackMinZ, fallbackMaxX, fallbackMaxZ);
	}

	private void EnsureParticipants()
	{
		var activePlayers = _api.GetActivePlayers();
		_racerCount = 0;

		for (int i = 0; i < activePlayers.Length && _racerCount < MaxRacers; i++)
		{
			PlayerId p = activePlayers[i];
			RacerState racer = _racers[_racerCount];
			racer.Active = true;
			racer.PlayerIndex = p.Value;
			racer.IsComputer = p.IsComputer;
			racer.DisplayName = string.IsNullOrWhiteSpace(p.Name) ? $"Racer {p.Value + 1}" : p.Name;
			racer.ColoredName = p.ColoredName;
			_racerCount++;
		}

		if (_racerCount == 1)
		{
			int desiredAiCount = 3;
			for (int candidate = 0; candidate < EcsSharedMemory.MAX_PLAYERS && desiredAiCount > 0; candidate++)
			{
				if (IsPlayerSeated(candidate)) continue;
				if (_api.AddComputerPlayer(candidate, $"Chariot AI {candidate}"))
				{
					PlayerId ai = _api.GetPlayer(candidate);
					RacerState racer = _racers[_racerCount];
					racer.Active = true;
					racer.PlayerIndex = candidate;
					racer.IsComputer = true;
					racer.DisplayName = ai.Name;
					racer.ColoredName = ai.ColoredName;
					_racerCount++;
					desiredAiCount--;
				}
			}
		}

		for (int slot = EcsSharedMemory.MAX_PLAYERS - 1; slot >= 0; slot--)
		{
			if (!IsPlayerSeated(slot))
			{
				_neutralSlot = slot;
				break;
			}
		}
	}

	private bool IsPlayerSeated(int playerIndex)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			if (_racers[i].PlayerIndex == playerIndex) return true;
		}
		return false;
	}

	private void SpawnRacers()
	{
		float startFacing = MathF.PI * 0.5f;

		for (int i = 0; i < _racerCount; i++)
		{
			RacerState racer = _racers[i];
			Vector3 spawn = ResolveStartPosition(racer.PlayerIndex, i);
			UnitId unit = _api.SpawnUnitForPlayer(UnitIds.ChariotRacer, new Vector2(spawn.X, spawn.Z), racer.PlayerIndex, true, true);
			if (!unit.IsValid) continue;

			racer.Unit = unit;
			racer.Position = unit.Position;
			racer.HeadingRadians = startFacing;
			racer.TargetHeading = startFacing;
			racer.Speed = 0f;
			racer.Lap = 1;
			racer.CheckpointStage = 0;
			racer.Rank = i + 1;
			racer.AiWaypointIndex = 0;
			racer.AiLaneOffset = ((i % 3) - 1) * 3.0f;

			unit.CommandsFrozen = true;
			unit.Invulnerable = true;
			unit.HideHealthAndManaBars = true;
			unit.Speed = 0f;
			_api.SetUnitLevel(unit, 1);
			_api.SetUnitFacing(unit, startFacing);
			_api.SetAbilityState(unit, AbilityIds.UsePowerup, true, false);
			_api.SetAbilityState(unit, AbilityIds.SteerLeft, false, true);
			_api.SetAbilityState(unit, AbilityIds.SteerRight, false, true);
			_api.SetAbilityState(unit, AbilityIds.SteerLeftStop, false, true);
			_api.SetAbilityState(unit, AbilityIds.SteerRightStop, false, true);

			if (!racer.IsComputer)
			{
				PlayerId player = _api.GetPlayer(racer.PlayerIndex);
				player.SelectUnit(unit);
				player.SetHudElementVisible(HudElement.ResourceBar, false);
				ApplyChaseCamera(racer.PlayerIndex, unit);
				player.SendMessage("CHARIOT RACER: Steer with [A]/[D] or Right-click | [Q] Turbo | [W] Item | [E] Drift | [R] Reverse");
				player.SendMessage("Tip: Hit [Q] right on GO for a Rocket Start! Chat '-chase' for 3rd person or '-top' for overhead.");
			}
		}
	}

	private Vector3 ResolveStartPosition(int playerIndex, int racerOrder)
	{
		Vector3 anchor = _api.GetSpawnAnchor(playerIndex);
		if (anchor != Vector3.Zero) return anchor;

		anchor = _api.GetSpawnAnchor(playerIndex + 1);
		if (anchor != Vector3.Zero) return anchor;

		int row = racerOrder / 2;
		int col = racerOrder % 2;
		float x = -8.0f - (row * 6.0f) - (col * 2.0f);
		float z = col == 0 ? -51.0f : -45.0f;
		return new Vector3(x, _api.GetTerrainHeight(x, z), z);
	}

	private void ApplyChaseCamera(int playerIndex, UnitId unit, bool reverseView = false)
	{
		if (!unit.IsValid) return;
		_api.SetPlayerCameraFollowUnit(
			playerIndex,
			unit,
			distance: 12.5f,
			heightOffset: 4.5f,
			pitchDegrees: -15.0f,
			yawOffsetDegrees: reverseView ? 180.0f : 0.0f,
			alignToUnitFacing: true,
			smoothing: 0f,
			lockCameraInput: true);
	}

	private void ApplyTopDownCamera(int playerIndex, UnitId unit)
	{
		if (!unit.IsValid) return;
		_api.SetPlayerCameraFollowUnit(
			playerIndex,
			unit,
			distance: 14.0f,
			heightOffset: 22.0f,
			pitchDegrees: -54.0f,
			yawOffsetDegrees: 0.0f,
			alignToUnitFacing: false,
			smoothing: 7.0f,
			lockCameraInput: true);
	}

	private void SpawnItemBoxes()
	{
		float[] zSlots = { -54.0f, -50.0f, -46.0f, -42.0f };
		for (int i = 0; i < 4; i++)
		{
			CreateItemBoxSlot(i, 46.0f, zSlots[i]);
			CreateItemBoxSlot(i + 4, -46.0f, -zSlots[i]);
		}
	}

	private void CreateItemBoxSlot(int index, float x, float z)
	{
		float y = _api.GetTerrainHeight(x, z);
		var pos = new Vector3(x, y, z);
		UnitId box = _api.SpawnUnitForPlayer(UnitIds.ItemCrystal, new Vector2(x, z), _neutralSlot, true, true);
		if (box.IsValid)
		{
			box.CommandsFrozen = true;
			box.Invulnerable = true;
			box.HideHealthAndManaBars = true;
		}
		_itemBoxes[index] = new ItemBoxSlot
		{
			Position = pos,
			Unit = box,
			RespawnTimer = 0f
		};
	}

	private void SetupInitialHudAndLeaderboard()
	{
		_api.SetLeaderboardVisible("CHARIOT RACER (3 LAPS)", true);
		PublishLeaderboard();
	}

	private void UpdateCountdown(float delta)
	{
		_countdownRemaining -= delta;
		int sec = (int)MathF.Ceiling(_countdownRemaining);

		if (sec >= 1 && sec <= 3 && sec != _lastAnnouncedSecond)
		{
			_lastAnnouncedSecond = sec;
			_api.BroadcastMessage($"Starting in {sec}...");
			_api.ShowFeedbackText($"{sec}...", new Vector3(1.0f, 0.85f, 0.2f));
		}

		if (_countdownRemaining <= 0f)
		{
			_raceStarted = true;
			_api.BroadcastMessage("GO! Race 3 Laps!");
			_api.ShowFeedbackText("GO!", new Vector3(0.2f, 1.0f, 0.35f));

			for (int i = 0; i < _racerCount; i++)
			{
				RacerState r = _racers[i];
				if (!r.Active || !r.Unit.IsValid) continue;

				if (!r.IsComputer)
				{
					_api.GetPlayer(r.PlayerIndex).SelectUnit(r.Unit);
				}

				if (r.RocketAttemptElapsed >= 0f && r.RocketAttemptElapsed <= RocketBoostWindowSeconds)
				{
					r.BoostTimer = 2.0f;
					r.Speed = TurboMaxSpeed;
					_api.CreateFloatingText("ROCKET START!", r.Position + new Vector3(0f, 2.5f, 0f), new Vector3(0.3f, 1.0f, 0.4f), 1.4f);
					_api.SpawnExpandingGroundRing(r.Position, 6f, 15f, 0.5f, new Vector3(1.0f, 0.8f, 0.1f));
				}
			}
		}
	}

	private void HandleUnitSelected(UnitId selectedUnit)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			RacerState r = _racers[i];
			if (!r.IsComputer && r.Active && r.Unit.IsValid && selectedUnit != r.Unit)
			{
				_api.GetPlayer(r.PlayerIndex).SelectUnit(r.Unit);
			}
		}
	}

	private void HandleUnitOrdered(UnitId unit, string order, Vector3 targetPosition)
	{
		RacerState? racer = FindRacerByUnit(unit);
		if (racer == null || racer.IsComputer) return;

		if (string.Equals(order, "move", StringComparison.OrdinalIgnoreCase) ||
			string.Equals(order, "move_queued", StringComparison.OrdinalIgnoreCase) ||
			string.Equals(order, "attack_move", StringComparison.OrdinalIgnoreCase) ||
			string.Equals(order, "attack_move_queued", StringComparison.OrdinalIgnoreCase))
		{
			_api.IssueStopOrder(racer.Unit);

			if (racer.ReverseTimer > 0f)
			{
				racer.ReverseTimer = 0f;
				if (!racer.IsComputer)
				{
					ApplyChaseCamera(racer.PlayerIndex, racer.Unit, reverseView: false);
				}
			}

			float dx = targetPosition.X - racer.Position.X;
			float dz = targetPosition.Z - racer.Position.Z;
			float distSq = dx * dx + dz * dz;

			if (distSq < 0.5f) return;

			float desiredHeading = MathF.Atan2(dx, dz);
			float angleDiff = WrapAngle(desiredHeading - racer.HeadingRadians);

			// If the player clicks behind the chariot (> 125 degrees away) while driving fast, do not steer backwards.
			if (MathF.Abs(angleDiff) > 2.2f && racer.Speed > 5.0f)
			{
				racer.BrakeTimer = 0.45f;
				return;
			}

			// Steer smoothly towards the target heading
			float maxClamp = racer.Speed > 5.0f ? 1.55f : MathF.PI;
			float clampedDiff = Math.Clamp(angleDiff, -maxClamp, maxClamp);
			racer.TargetHeading = WrapAngle(racer.HeadingRadians + clampedDiff);
			racer.SteerTarget = targetPosition;
			racer.HasSteerTarget = true;
			racer.KeySteerInput = 0f;
		}
		else if (string.Equals(order, "stop", StringComparison.OrdinalIgnoreCase) ||
				 string.Equals(order, "hold", StringComparison.OrdinalIgnoreCase))
		{
			_api.IssueStopOrder(racer.Unit);

			if (racer.ReverseTimer > 0f)
			{
				racer.ReverseTimer = 0f;
				if (!racer.IsComputer)
				{
					ApplyChaseCamera(racer.PlayerIndex, racer.Unit, reverseView: false);
				}
			}
			racer.HasSteerTarget = false;
			racer.BrakeTimer = 0.6f;
		}
	}

	private void HandleSpellCast(UnitId caster, string abilityId, Vector3 targetPosition)
	{
		_ = targetPosition;
		RacerState? racer = FindRacerByUnit(caster);
		if (racer == null) return;

		if (string.Equals(abilityId, AbilityIds.TurboBoost, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted)
			{
				racer.RocketAttemptElapsed = CountdownDurationSeconds - _countdownRemaining;
				_api.CreateFloatingText("REV UP!", racer.Position + new Vector3(0f, 2.2f, 0f), new Vector3(1.0f, 0.75f, 0.2f), 0.7f);
				return;
			}

			TriggerBoost(racer, 7.5f, "TURBO BOOST!");
		}
		else if (string.Equals(abilityId, AbilityIds.UsePowerup, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted) return;
			ActivateHeldPowerUp(racer);
		}
		else if (string.Equals(abilityId, AbilityIds.DriftHop, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted) return;
			racer.DriftTimer = 1.4f;
			racer.PendingMiniTurbo = true;
			_api.CreateFloatingText("DRIFT!", racer.Position + new Vector3(0f, 2.1f, 0f), new Vector3(0.4f, 0.9f, 1.0f), 0.7f);
		}
		else if (string.Equals(abilityId, AbilityIds.BrakeReverse, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted) return;
			racer.ReverseTimer = 1.3f;
			racer.Speed = 0f;
			racer.HasSteerTarget = false;
			racer.CurrentTurnVelocity = 0f;
			if (!racer.IsComputer)
			{
				ApplyChaseCamera(racer.PlayerIndex, racer.Unit, reverseView: true);
			}
			_api.CreateFloatingText("REVERSE", racer.Position + new Vector3(0f, 2.2f, 0f), new Vector3(1.0f, 0.8f, 0.2f), 0.7f);
		}
		else if (string.Equals(abilityId, AbilityIds.SteerLeft, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted) return;
			racer.KeySteerInput = 1.0f;
		}
		else if (string.Equals(abilityId, AbilityIds.SteerLeftStop, StringComparison.OrdinalIgnoreCase))
		{
			if (racer.KeySteerInput > 0f) racer.KeySteerInput = 0f;
		}
		else if (string.Equals(abilityId, AbilityIds.SteerRight, StringComparison.OrdinalIgnoreCase))
		{
			if (!_raceStarted) return;
			racer.KeySteerInput = -1.0f;
		}
		else if (string.Equals(abilityId, AbilityIds.SteerRightStop, StringComparison.OrdinalIgnoreCase))
		{
			if (racer.KeySteerInput < 0f) racer.KeySteerInput = 0f;
		}
	}

	private void HandlePlayerChatMessage(string message, int playerIndex)
	{
		RacerState? racer = FindRacerByPlayer(playerIndex);
		if (racer == null || !racer.Unit.IsValid) return;

		string trimmed = message.Trim().ToLowerInvariant();
		PlayerId player = _api.GetPlayer(playerIndex);

		if (trimmed == "-top" || trimmed == "-iso")
		{
			ApplyTopDownCamera(playerIndex, racer.Unit);
			player.SendMessage("Camera: Elevated Racing View");
		}
		else if (trimmed == "-chase")
		{
			ApplyChaseCamera(playerIndex, racer.Unit);
			player.SendMessage("Camera: Chase View");
		}
		else if (trimmed == "-wide")
		{
			_api.SetPlayerCameraFollowUnit(playerIndex, racer.Unit, 20f, 8f, -22f, 0f, true, 3.0f, true);
			player.SendMessage("Camera: Wide Chase View");
		}
		else if (trimmed == "-stuck")
		{
			RecoverRacerToTrack(racer);
		}
	}

	private void HandlePlayerLeft(int playerIndex)
	{
		RacerState? racer = FindRacerByPlayer(playerIndex);
		if (racer != null)
		{
			racer.IsComputer = true;
		}
	}

	private void UpdateRacers(float delta)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			RacerState racer = _racers[i];
			if (!racer.Active || !racer.Unit.IsValid || racer.Unit.IsDead) continue;

			if (racer.BoostPadCooldown > 0f) racer.BoostPadCooldown -= delta;
			if (racer.ShockedTimer > 0f) racer.ShockedTimer -= delta;

			if (racer.StarTimer > 0f)
			{
				racer.StarTimer -= delta;
				racer.StarVfxCooldown -= delta;
				if (racer.StarVfxCooldown <= 0f)
				{
					racer.StarVfxCooldown = 0.25f;
					_api.SpawnExpandingGroundRing(racer.Position, 3.2f, 12f, 0.35f, new Vector3(1.0f, 0.9f, 0.2f));
				}
			}

			if (racer.BoostTimer > 0f)
			{
				racer.BoostTimer -= delta;
				racer.TurboVfxCooldown -= delta;
				if (racer.TurboVfxCooldown <= 0f)
				{
					racer.TurboVfxCooldown = 0.12f;
					_api.SpawnVisualEffect("fireblast", racer.Position, 0.85f);
				}
			}

			if (racer.DriftTimer > 0f)
			{
				racer.DriftTimer -= delta;
				if (racer.DriftTimer <= 0f && racer.PendingMiniTurbo)
				{
					racer.PendingMiniTurbo = false;
					TriggerBoost(racer, 1.0f, "MINI-TURBO!");
				}
			}

			if (racer.BrakeTimer > 0f) racer.BrakeTimer -= delta;

			if (racer.ReverseTimer > 0f)
			{
				racer.ReverseTimer -= delta;
				if (racer.ReverseTimer <= 0f && !racer.IsComputer)
				{
					ApplyChaseCamera(racer.PlayerIndex, racer.Unit, reverseView: false);
				}
			}

			if (racer.SpinOutTimer > 0f)
			{
				racer.SpinOutTimer -= delta;
				racer.Speed = MathF.Max(0f, racer.Speed - BrakeDecelerationRate * delta);
			}
			else
			{
				if (racer.IsComputer || racer.Finished)
				{
					UpdateAiSteering(racer, delta);
				}

				UpdateSteerAndThrottle(racer, delta);
			}

			AdvanceKartPosition(racer, delta);
			CheckTrackRegionsAndLaps(racer);
		}
	}

	private void UpdateAiSteering(RacerState racer, float delta)
	{
		Vector2 wp = _waypoints[racer.AiWaypointIndex];
		int nextIdx = (racer.AiWaypointIndex + 1) % WaypointCount;
		Vector2 nextWp = _waypoints[nextIdx];
		Vector2 dir = nextWp - wp;
		float len = dir.Length();
		Vector2 perp = len > 0.001f ? new Vector2(-dir.Y / len, dir.X / len) : Vector2.UnitY;
		Vector2 aim = wp + perp * racer.AiLaneOffset;

		float distSq = Vector2.DistanceSquared(new Vector2(racer.Position.X, racer.Position.Z), aim);
		if (distSq < 11.0f * 11.0f)
		{
			racer.AiWaypointIndex = nextIdx;
			racer.AiLaneOffset = _api.RandomFloat(-4.5f, 4.5f);
		}

		racer.SteerTarget = new Vector3(aim.X, racer.Position.Y, aim.Y);
		racer.HasSteerTarget = true;

		if (racer.Finished) return;

		if (racer.AiTurboCooldown > 0f) racer.AiTurboCooldown -= delta;

		racer.AiDecisionTimer -= delta;
		if (racer.AiDecisionTimer > 0f) return;
		racer.AiDecisionTimer = _api.RandomFloat(0.6f, 1.4f);

		if (racer.HeldItem != PowerUpType.None)
		{
			ActivateHeldPowerUp(racer);
		}
		else if (racer.AiTurboCooldown <= 0f && _api.RandomInt(0, 3) == 0)
		{
			TriggerBoost(racer, 1.6f, "AI TURBO");
			racer.AiTurboCooldown = 7.0f;
		}
	}

	private void UpdateSteerAndThrottle(RacerState racer, float delta)
	{
		float targetTurnRate = 0f;
		float maxTurn = racer.BoostTimer > 0f
			? (racer.DriftTimer > 0f ? BoostDriftTurnRate : BoostTurnRate)
			: (racer.DriftTimer > 0f ? DriftTurnRate : BaseTurnRate);

		if (racer.IsComputer || racer.Finished)
		{
			if (racer.HasSteerTarget)
			{
				float dx = racer.SteerTarget.X - racer.Position.X;
				float dz = racer.SteerTarget.Z - racer.Position.Z;
				float distSq = dx * dx + dz * dz;

				if (distSq > 0.25f)
				{
					float targetYaw = MathF.Atan2(dx, dz);
					float yawDiff = WrapAngle(targetYaw - racer.HeadingRadians);
					targetTurnRate = Math.Clamp(yawDiff * (racer.BoostTimer > 0f ? 2.2f : 3.5f), -maxTurn, maxTurn);
				}
			}
		}
		else
		{
			if (racer.ReverseTimer <= 0f)
			{
				if (racer.KeySteerInput != 0f)
				{
					targetTurnRate = racer.KeySteerInput * maxTurn;
					racer.HasSteerTarget = false;
				}
				else if (racer.HasSteerTarget)
				{
					float yawDiff = WrapAngle(racer.TargetHeading - racer.HeadingRadians);

					if (MathF.Abs(yawDiff) < 0.025f)
					{
						racer.HasSteerTarget = false;
					}
					else
					{
						targetTurnRate = Math.Clamp(yawDiff * (racer.BoostTimer > 0f ? 2.5f : 4.5f), -maxTurn, maxTurn);
					}
				}
			}
		}

		if (racer.BoostTimer > 0f)
		{
			racer.CurrentTurnVelocity = MoveTowards(racer.CurrentTurnVelocity, targetTurnRate, BoostTurnInertia * delta);
		}
		else
		{
			racer.CurrentTurnVelocity = targetTurnRate;
		}

		if (MathF.Abs(racer.CurrentTurnVelocity) > 0.001f)
		{
			racer.HeadingRadians = WrapAngle(racer.HeadingRadians + racer.CurrentTurnVelocity * delta);
		}

		bool offroad = !IsOnRoad(racer.Position.X, racer.Position.Z);
		float targetMaxSpeed = BaseMaxSpeed;

		if (racer.StarTimer > 0f)
		{
			targetMaxSpeed = StarMaxSpeed;
		}
		else if (racer.BoostTimer > 0f)
		{
			targetMaxSpeed = TurboMaxSpeed;
		}
		else if (racer.ShockedTimer > 0f)
		{
			targetMaxSpeed = BaseMaxSpeed * 0.5f;
		}
		else if (offroad)
		{
			targetMaxSpeed = OffroadMaxSpeed;
		}
		else if (racer.DriftTimer > 0f)
		{
			targetMaxSpeed = BaseMaxSpeed * 0.92f;
		}

		if (racer.Finished) targetMaxSpeed = BaseMaxSpeed * 0.6f;

		if (racer.BrakeTimer > 0f)
		{
			racer.Speed = MathF.Max(2.0f, racer.Speed - BrakeDecelerationRate * delta);
		}
		else if (racer.Speed < targetMaxSpeed)
		{
			float accel = racer.BoostTimer > 0f || racer.StarTimer > 0f ? AccelerationRate * 3.2f : AccelerationRate;
			racer.Speed = MathF.Min(targetMaxSpeed, racer.Speed + accel * delta);
		}
		else if (racer.Speed > targetMaxSpeed)
		{
			racer.Speed = MathF.Max(targetMaxSpeed, racer.Speed - CoastDecelerationRate * 2.0f * delta);
		}
	}

	private void AdvanceKartPosition(RacerState racer, float delta)
	{
		float forwardX = MathF.Sin(racer.HeadingRadians);
		float forwardZ = MathF.Cos(racer.HeadingRadians);

		float moveDist = racer.ReverseTimer > 0f ? (-7.0f * delta) : (racer.Speed * delta);
		float nextX = racer.Position.X + forwardX * moveDist;
		float nextZ = racer.Position.Z + forwardZ * moveDist;

		if (!_api.IsPointPassable(nextX, nextZ, PathingFlags.Ground))
		{
			racer.HasSteerTarget = false;
			racer.CurrentTurnVelocity = 0f;

			bool canSlideX = _api.IsPointPassable(nextX, racer.Position.Z, PathingFlags.Ground);
			bool canSlideZ = _api.IsPointPassable(racer.Position.X, nextZ, PathingFlags.Ground);

			if (canSlideX)
			{
				nextZ = racer.Position.Z;
				racer.Speed *= 0.85f;
			}
			else if (canSlideZ)
			{
				nextX = racer.Position.X;
				racer.Speed *= 0.85f;
			}
			else
			{
				nextX = racer.Position.X;
				nextZ = racer.Position.Z;
				racer.Speed = 0f;
				if (racer.BoostTimer > 0f)
				{
					racer.BoostTimer = 0f;
					if (!racer.IsComputer)
					{
						_api.ShakePlayerCamera(racer.PlayerIndex, 0.6f, 0.35f);
					}
				}
				if (racer.ReverseTimer > 0f)
				{
					racer.ReverseTimer = 0f;
					if (!racer.IsComputer)
					{
						ApplyChaseCamera(racer.PlayerIndex, racer.Unit, reverseView: false);
					}
				}
			}
		}

		float nextY = _api.GetTerrainHeight(nextX, nextZ);
		racer.Position = new Vector3(nextX, nextY, nextZ);
		_api.TeleportUnit(racer.Unit, racer.Position);
		_api.SetUnitFacing(racer.Unit, racer.HeadingRadians);
		_api.SetUnitAnimation(racer.Unit, racer.Speed > 1.5f || racer.ReverseTimer > 0f ? "Move" : "Idle");
	}

	private void ResolveKartCollisions()
	{
		float minDist = KartRadius * 2.0f;
		float minDistSq = minDist * minDist;

		for (int i = 0; i < _racerCount; i++)
		{
			RacerState a = _racers[i];
			if (!a.Active || !a.Unit.IsValid) continue;

			for (int j = i + 1; j < _racerCount; j++)
			{
				RacerState b = _racers[j];
				if (!b.Active || !b.Unit.IsValid) continue;

				float dx = b.Position.X - a.Position.X;
				float dz = b.Position.Z - a.Position.Z;
				float distSq = dx * dx + dz * dz;
				if (distSq <= 0.0001f || distSq >= minDistSq) continue;

				float dist = MathF.Sqrt(distSq);
				float overlap = (minDist - dist) * 0.5f;
				float nx = dx / dist;
				float nz = dz / dist;

				if (a.StarTimer > 0f && b.StarTimer <= 0f)
				{
					SpinOutRacer(b, "STAR SMASH!");
				}
				else if (b.StarTimer > 0f && a.StarTimer <= 0f)
				{
					SpinOutRacer(a, "STAR SMASH!");
				}

				TryNudgeRacer(a, -nx * overlap, -nz * overlap);
				TryNudgeRacer(b, nx * overlap, nz * overlap);
			}
		}
	}

	private void TryNudgeRacer(RacerState racer, float offsetX, float offsetZ)
	{
		float tx = racer.Position.X + offsetX;
		float tz = racer.Position.Z + offsetZ;
		if (!_api.IsPointPassable(tx, tz, PathingFlags.Ground)) return;

		racer.Position = new Vector3(tx, _api.GetTerrainHeight(tx, tz), tz);
		_api.TeleportUnit(racer.Unit, racer.Position);
	}

	private void CheckTrackRegionsAndLaps(RacerState racer)
	{
		if (racer.BoostPadCooldown <= 0f &&
			(_boostPadEastRegion.Contains(racer.Position) || _boostPadWestRegion.Contains(racer.Position)))
		{
			racer.BoostPadCooldown = 1.25f;
			TriggerBoost(racer, 1.5f, "BOOST PAD!");
		}

		if (racer.Finished) return;

		if (racer.CheckpointStage == 0 && _checkpoint1Region.Contains(racer.Position))
		{
			racer.CheckpointStage = 1;
		}
		else if (racer.CheckpointStage == 1 && _checkpoint2Region.Contains(racer.Position))
		{
			racer.CheckpointStage = 2;
		}
		else if (racer.CheckpointStage == 2 && _checkpoint3Region.Contains(racer.Position))
		{
			racer.CheckpointStage = 3;
		}
		else if (racer.CheckpointStage == 3 && _finishRegion.Contains(racer.Position))
		{
			racer.CheckpointStage = 0;
			racer.Lap++;

			if (racer.Lap > TotalLaps)
			{
				racer.Finished = true;
				racer.FinishTime = _raceElapsed;
				_finishedCount++;
				racer.FinishOrder = _finishedCount;

				_api.BroadcastMessage($"{racer.ColoredName} finished in position #{racer.FinishOrder} ({racer.FinishTime:F1}s)!");
				_api.CreateFloatingText($"FINISH #{racer.FinishOrder}!", racer.Position + new Vector3(0f, 3.0f, 0f), new Vector3(1.0f, 0.9f, 0.2f), 2.5f);

				if (racer.FinishOrder == 1)
				{
					_winnerRacerIndex = FindRacerIndex(racer);
					_endGameTimer = 2.0f;
				}
			}
			else
			{
				_api.SetUnitLevel(racer.Unit, racer.Lap);
				if (!racer.IsComputer)
				{
					string lapMsg = racer.Lap == TotalLaps ? "FINAL LAP!" : $"LAP {racer.Lap} / {TotalLaps}";
					_api.GetPlayer(racer.PlayerIndex).ShowFeedbackText(lapMsg, new Vector3(0.3f, 0.95f, 1.0f));
					_api.GetPlayer(racer.PlayerIndex).SendMessage(lapMsg);
				}
			}
		}

		float wpProgress = ComputeWaypointProgress(racer.Position, racer.CheckpointStage);
		racer.RaceScore = racer.Finished
			? 1000000.0f - racer.FinishTime
			: (racer.Lap * 100.0f) + (racer.CheckpointStage * 25.0f) + wpProgress;
	}

	private float ComputeWaypointProgress(Vector3 pos, int checkpointStage)
	{
		int startWp = checkpointStage * 4;
		int endWp = startWp + 4;
		float bestDistSq = float.MaxValue;
		int bestWp = startWp;

		for (int i = startWp; i <= endWp; i++)
		{
			Vector2 wp = _waypoints[i % WaypointCount];
			float dx = pos.X - wp.X;
			float dz = pos.Z - wp.Y;
			float dSq = dx * dx + dz * dz;
			if (dSq < bestDistSq)
			{
				bestDistSq = dSq;
				bestWp = i;
			}
		}

		return (bestWp - startWp) * 5.0f + MathF.Max(0f, 4.9f - MathF.Sqrt(bestDistSq) * 0.08f);
	}

	private void UpdateItemBoxes(float delta)
	{
		for (int i = 0; i < ItemBoxCount; i++)
		{
			ItemBoxSlot box = _itemBoxes[i];
			if (box == null) continue;

			if (!box.Unit.IsValid)
			{
				box.RespawnTimer -= delta;
				if (box.RespawnTimer <= 0f)
				{
					UnitId respawned = _api.SpawnUnitForPlayer(UnitIds.ItemCrystal, new Vector2(box.Position.X, box.Position.Z), _neutralSlot, true, true);
					if (respawned.IsValid)
					{
						respawned.CommandsFrozen = true;
						respawned.Invulnerable = true;
						respawned.HideHealthAndManaBars = true;
						box.Unit = respawned;
					}
				}
				continue;
			}

			for (int r = 0; r < _racerCount; r++)
			{
				RacerState racer = _racers[r];
				if (!racer.Active || !racer.Unit.IsValid) continue;

				float dx = racer.Position.X - box.Position.X;
				float dz = racer.Position.Z - box.Position.Z;
				if (dx * dx + dz * dz > 2.4f * 2.4f) continue;

				_api.DestroyUnit(box.Unit, false, false);
				box.Unit = UnitId.Invalid;
				box.RespawnTimer = 6.0f;
				_api.SpawnExpandingBurstSphere(box.Position, 3.0f, 12f, 0.35f, new Vector3(1.0f, 0.85f, 0.2f));

				if (racer.HeldItem == PowerUpType.None)
				{
					GrantRandomPowerUp(racer);
				}
				break;
			}
		}
	}

	private void GrantRandomPowerUp(RacerState racer)
	{
		int roll = _api.RandomInt(0, 99);
		PowerUpType item;

		if (racer.Rank <= 1)
		{
			item = roll < 40 ? PowerUpType.SpikeTrap : roll < 75 ? PowerUpType.GreenShell : PowerUpType.TurboMushroom;
		}
		else if (racer.Rank >= _racerCount)
		{
			item = roll < 28 ? PowerUpType.StarPower : roll < 52 ? PowerUpType.LightningBolt : roll < 78 ? PowerUpType.RedShell : PowerUpType.TurboMushroom;
		}
		else
		{
			item = roll < 25 ? PowerUpType.TurboMushroom :
				roll < 50 ? PowerUpType.GreenShell :
				roll < 72 ? PowerUpType.RedShell :
				roll < 88 ? PowerUpType.SpikeTrap :
				PowerUpType.StarPower;
		}

		racer.HeldItem = item;
		_api.SetAbilityState(racer.Unit, AbilityIds.UsePowerup, false, false);

		string label = FormatPowerUpName(item);
		_api.CreateFloatingText($"+{label}", racer.Position + new Vector3(0f, 2.4f, 0f), new Vector3(1.0f, 0.9f, 0.25f), 1.3f);

		if (!racer.IsComputer)
		{
			_api.GetPlayer(racer.PlayerIndex).SendMessage($"Item collected: [{label}] — Press [W] to use!");
		}
	}

	private void ActivateHeldPowerUp(RacerState racer)
	{
		PowerUpType item = racer.HeldItem;
		if (item == PowerUpType.None) return;

		racer.HeldItem = PowerUpType.None;
		_api.SetAbilityState(racer.Unit, AbilityIds.UsePowerup, true, false);

		switch (item)
		{
			case PowerUpType.TurboMushroom:
				TriggerBoost(racer, 2.2f, "MUSHROOM BOOST!");
				break;

			case PowerUpType.GreenShell:
				LaunchShell(racer, isHoming: false);
				break;

			case PowerUpType.RedShell:
				LaunchShell(racer, isHoming: true);
				break;

			case PowerUpType.SpikeTrap:
				DropHazardBehind(racer);
				break;

			case PowerUpType.LightningBolt:
				CastLightningShock(racer);
				break;

			case PowerUpType.StarPower:
				racer.StarTimer = 4.5f;
				racer.SpinOutTimer = 0f;
				racer.VisualSpinOffset = 0f;
				racer.ShockedTimer = 0f;
				_api.CreateFloatingText("STAR POWER!", racer.Position + new Vector3(0f, 2.8f, 0f), new Vector3(1.0f, 0.95f, 0.2f), 1.6f);
				_api.BroadcastMessage($"{racer.ColoredName} activated Star Power!");
				break;
		}
	}

	private void LaunchShell(RacerState racer, bool isHoming)
	{
		for (int i = 0; i < MaxProjectiles; i++)
		{
			ShellProjectileSlot slot = _projectiles[i];
			if (slot.Active) continue;

			float spawnX = racer.Position.X + MathF.Sin(racer.HeadingRadians) * 2.2f;
			float spawnZ = racer.Position.Z + MathF.Cos(racer.HeadingRadians) * 2.2f;
			UnitId proj = _api.SpawnUnitForPlayer(UnitIds.ShellProjectile, new Vector2(spawnX, spawnZ), _neutralSlot, false, true);
			if (proj.IsValid)
			{
				proj.CommandsFrozen = true;
				proj.Invulnerable = true;
				proj.HideHealthAndManaBars = true;
				_api.SetUnitColor(proj, isHoming ? new Vector3(1.0f, 0.25f, 0.2f) : new Vector3(0.2f, 1.0f, 0.35f));
			}

			slot.Active = true;
			slot.Unit = proj;
			slot.Position = new Vector3(spawnX, _api.GetTerrainHeight(spawnX, spawnZ), spawnZ);
			slot.HeadingRadians = racer.HeadingRadians;
			slot.Speed = isHoming ? 32.0f : 34.0f;
			slot.OwnerPlayerIndex = racer.PlayerIndex;
			slot.IsHoming = isHoming;
			slot.BouncesRemaining = isHoming ? 1 : 3;
			slot.GraceTimer = 0.2f;
			slot.RemainingLifetime = 5.0f;
			return;
		}
	}

	private void DropHazardBehind(RacerState racer)
	{
		for (int i = 0; i < MaxHazards; i++)
		{
			HazardSlot slot = _hazards[i];
			if (slot.Active) continue;

			float dropX = racer.Position.X - MathF.Sin(racer.HeadingRadians) * 2.4f;
			float dropZ = racer.Position.Z - MathF.Cos(racer.HeadingRadians) * 2.4f;
			UnitId hazardUnit = _api.SpawnUnitForPlayer(UnitIds.TrackHazard, new Vector2(dropX, dropZ), _neutralSlot, false, true);
			if (hazardUnit.IsValid)
			{
				hazardUnit.CommandsFrozen = true;
				hazardUnit.Invulnerable = true;
				hazardUnit.HideHealthAndManaBars = true;
			}

			slot.Active = true;
			slot.Unit = hazardUnit;
			slot.Position = new Vector3(dropX, _api.GetTerrainHeight(dropX, dropZ), dropZ);
			slot.OwnerPlayerIndex = racer.PlayerIndex;
			slot.GraceTimer = 0.7f;
			slot.RemainingLifetime = 25.0f;
			return;
		}
	}

	private void CastLightningShock(RacerState caster)
	{
		_api.BroadcastMessage($"{caster.ColoredName} unleashed LIGHTNING SHOCK!");
		for (int i = 0; i < _racerCount; i++)
		{
			RacerState rival = _racers[i];
			if (!rival.Active || rival.PlayerIndex == caster.PlayerIndex || rival.StarTimer > 0f) continue;

			rival.ShockedTimer = 2.0f;
			SpinOutRacer(rival, "ZAP!");
			_api.SpawnVisualEffect("lightning", rival.Position, 1.2f);
			if (!rival.IsComputer)
			{
				_api.ShakePlayerCamera(rival.PlayerIndex, 0.9f, 0.45f);
			}
		}
	}

	private void UpdateHazards(float delta)
	{
		for (int i = 0; i < MaxHazards; i++)
		{
			HazardSlot slot = _hazards[i];
			if (!slot.Active) continue;

			slot.RemainingLifetime -= delta;
			if (slot.GraceTimer > 0f) slot.GraceTimer -= delta;

			if (slot.RemainingLifetime <= 0f)
			{
				ClearHazard(slot);
				continue;
			}

			for (int r = 0; r < _racerCount; r++)
			{
				RacerState racer = _racers[r];
				if (!racer.Active || !racer.Unit.IsValid) continue;
				if (slot.GraceTimer > 0f && racer.PlayerIndex == slot.OwnerPlayerIndex) continue;

				float dx = racer.Position.X - slot.Position.X;
				float dz = racer.Position.Z - slot.Position.Z;
				if (dx * dx + dz * dz > 1.9f * 1.9f) continue;

				if (racer.StarTimer <= 0f)
				{
					SpinOutRacer(racer, "TRAPPED!");
				}
				ClearHazard(slot);
				break;
			}
		}
	}

	private void UpdateProjectiles(float delta)
	{
		for (int i = 0; i < MaxProjectiles; i++)
		{
			ShellProjectileSlot slot = _projectiles[i];
			if (!slot.Active) continue;

			slot.RemainingLifetime -= delta;
			if (slot.GraceTimer > 0f) slot.GraceTimer -= delta;

			if (slot.RemainingLifetime <= 0f)
			{
				ClearProjectile(slot);
				continue;
			}

			if (slot.IsHoming)
			{
				RacerState? target = FindClosestRacer(slot.Position, slot.OwnerPlayerIndex);
				if (target != null)
				{
					float desired = MathF.Atan2(target.Position.X - slot.Position.X, target.Position.Z - slot.Position.Z);
					float diff = WrapAngle(desired - slot.HeadingRadians);
					float maxTurn = 4.2f * delta;
					slot.HeadingRadians = WrapAngle(slot.HeadingRadians + Math.Clamp(diff, -maxTurn, maxTurn));
				}
			}

			float fx = MathF.Sin(slot.HeadingRadians);
			float fz = MathF.Cos(slot.HeadingRadians);
			float nextX = slot.Position.X + fx * slot.Speed * delta;
			float nextZ = slot.Position.Z + fz * slot.Speed * delta;

			if (!_api.IsPointPassable(nextX, nextZ, PathingFlags.Ground))
			{
				if (slot.BouncesRemaining <= 0)
				{
					ClearProjectile(slot);
					continue;
				}
				slot.BouncesRemaining--;

				bool bounceX = !_api.IsPointPassable(nextX, slot.Position.Z, PathingFlags.Ground);
				if (bounceX)
				{
					fx = -fx;
					nextX = slot.Position.X;
				}
				else
				{
					fz = -fz;
					nextZ = slot.Position.Z;
				}
				slot.HeadingRadians = MathF.Atan2(fx, fz);
			}

			slot.Position = new Vector3(nextX, _api.GetTerrainHeight(nextX, nextZ), nextZ);
			if (slot.Unit.IsValid)
			{
				_api.TeleportUnit(slot.Unit, slot.Position);
				_api.SetUnitFacing(slot.Unit, WrapAngle(slot.HeadingRadians));
			}

			for (int r = 0; r < _racerCount; r++)
			{
				RacerState racer = _racers[r];
				if (!racer.Active || !racer.Unit.IsValid) continue;
				if (slot.GraceTimer > 0f && racer.PlayerIndex == slot.OwnerPlayerIndex) continue;

				float dx = racer.Position.X - slot.Position.X;
				float dz = racer.Position.Z - slot.Position.Z;
				if (dx * dx + dz * dz > 2.1f * 2.1f) continue;

				if (racer.StarTimer <= 0f)
				{
					SpinOutRacer(racer, "SHELL HIT!");
				}
				ClearProjectile(slot);
				break;
			}
		}
	}

	private void ClearHazard(HazardSlot slot)
	{
		if (slot.Unit.IsValid)
		{
			_api.SpawnExpandingBurstSphere(slot.Position, 2.5f, 10f, 0.3f, new Vector3(1.0f, 0.5f, 0.1f));
			_api.DestroyUnit(slot.Unit, false, false);
		}
		slot.Unit = UnitId.Invalid;
		slot.Active = false;
	}

	private void ClearProjectile(ShellProjectileSlot slot)
	{
		if (slot.Unit.IsValid)
		{
			_api.SpawnExpandingBurstSphere(slot.Position, 2.8f, 12f, 0.3f, slot.IsHoming ? new Vector3(1.0f, 0.25f, 0.2f) : new Vector3(0.2f, 1.0f, 0.35f));
			_api.DestroyUnit(slot.Unit, false, false);
		}
		slot.Unit = UnitId.Invalid;
		slot.Active = false;
	}

	private void TriggerBoost(RacerState racer, float duration, string label)
	{
		if (racer.SpinOutTimer > 0f) return;
		racer.BoostTimer = MathF.Max(racer.BoostTimer, duration);
		racer.Speed = MathF.Max(racer.Speed, TurboMaxSpeed);
		_api.CreateFloatingText(label, racer.Position + new Vector3(0f, 2.5f, 0f), new Vector3(1.0f, 0.75f, 0.15f), 1.2f);
		_api.SpawnExpandingGroundRing(racer.Position, 5.0f, 16f, 0.35f, new Vector3(1.0f, 0.6f, 0.1f));
		_api.SpawnVisualEffect("fireblast", racer.Position, 1.4f);
		if (!racer.IsComputer)
		{
			_api.ShakePlayerCamera(racer.PlayerIndex, 0.65f, 0.45f);
		}
	}

	private void SpinOutRacer(RacerState racer, string reason)
	{
		if (racer.SpinOutTimer > 0f) return;
		racer.SpinOutTimer = 1.05f;
		racer.BoostTimer = 0f;
		racer.DriftTimer = 0f;
		racer.PendingMiniTurbo = false;
		racer.HasSteerTarget = false;
		racer.KeySteerInput = 0f;
		racer.CurrentTurnVelocity = 0f;
		_api.CreateFloatingText(reason, racer.Position + new Vector3(0f, 2.6f, 0f), new Vector3(1.0f, 0.25f, 0.25f), 1.2f);
		if (!racer.IsComputer)
		{
			_api.ShakePlayerCamera(racer.PlayerIndex, 0.7f, 0.35f);
		}
	}

	private void RecoverRacerToTrack(RacerState racer)
	{
		int wpIndex = FindClosestWaypointIndex(racer.Position);
		Vector2 wp = _waypoints[wpIndex];
		Vector2 nextWp = _waypoints[(wpIndex + 1) % WaypointCount];

		racer.Position = new Vector3(wp.X, _api.GetTerrainHeight(wp.X, wp.Y), wp.Y);
		racer.HeadingRadians = MathF.Atan2(nextWp.X - wp.X, nextWp.Y - wp.Y);
		racer.TargetHeading = racer.HeadingRadians;
		racer.Speed = 6.0f;
		racer.ReverseTimer = 0f;
		racer.HasSteerTarget = false;
		racer.KeySteerInput = 0f;
		racer.CurrentTurnVelocity = 0f;
		_api.TeleportUnit(racer.Unit, racer.Position);
		_api.SetUnitFacing(racer.Unit, racer.HeadingRadians);
		if (!racer.IsComputer)
		{
			ApplyChaseCamera(racer.PlayerIndex, racer.Unit);
		}
		_api.CreateFloatingText("RECOVER!", racer.Position + new Vector3(0f, 2.3f, 0f), new Vector3(0.4f, 0.9f, 1.0f), 1.0f);
	}

	private void UpdateRankings()
	{
		for (int i = 0; i < _racerCount; i++) _rankedIndices[i] = i;

		for (int i = 0; i < _racerCount - 1; i++)
		{
			for (int j = i + 1; j < _racerCount; j++)
			{
				if (_racers[_rankedIndices[j]].RaceScore > _racers[_rankedIndices[i]].RaceScore)
				{
					int tmp = _rankedIndices[i];
					_rankedIndices[i] = _rankedIndices[j];
					_rankedIndices[j] = tmp;
				}
			}
		}

		for (int rank = 0; rank < _racerCount; rank++)
		{
			_racers[_rankedIndices[rank]].Rank = rank + 1;
		}
	}

	private void PublishLeaderboard()
	{
		for (int rank = 0; rank < _racerCount; rank++)
		{
			RacerState racer = _racers[_rankedIndices[rank]];
			string lapText = racer.Finished ? $"FIN ({racer.FinishTime:F1}s)" : $"Lap {racer.Lap}/{TotalLaps}";
			string itemText = racer.HeldItem == PowerUpType.None ? string.Empty : $" | [{FormatPowerUpName(racer.HeldItem)}]";
			_api.SetLeaderboardValue($"#{rank + 1}", $"{racer.ColoredName} — {lapText}{itemText}");
		}
	}

	private void FinalizeMatchOutcome()
	{
		if (_raceEnded) return;
		_raceEnded = true;

		_api.SetSummaryTableHeaders("Racer", "Rank", "Lap", "Status");
		for (int rank = 0; rank < _racerCount; rank++)
		{
			RacerState racer = _racers[_rankedIndices[rank]];
			string status = racer.Finished ? $"{racer.FinishTime:F1}s" : $"Lap {racer.Lap}/{TotalLaps}";
			_api.SetSummaryTableRow(racer.ColoredName, $"#{rank + 1}", $"{Math.Min(racer.Lap, TotalLaps)}/{TotalLaps}", status);
		}
		_api.ShowSummaryTable("Chariot Racer Results", true);

		if (_winnerRacerIndex < 0) return;

		RacerState winner = _racers[_winnerRacerIndex];
		_api.TriggerPlayerVictory(winner.PlayerIndex);
		for (int i = 0; i < _racerCount; i++)
		{
			if (i == _winnerRacerIndex) continue;
			_api.TriggerPlayerDefeat(_racers[i].PlayerIndex, $"{winner.DisplayName} won the race!");
		}
	}

	private bool IsOnRoad(float wx, float wz)
	{
		float cx = Math.Clamp(wx, -40.0f, 40.0f);
		float dx = wx - cx;
		float distFromSpine = MathF.Sqrt(dx * dx + wz * wz);
		return MathF.Abs(distFromSpine - 48.0f) <= TrackHalfWidth;
	}

	private RacerState? FindClosestRacer(Vector3 origin, int excludedPlayerIndex)
	{
		RacerState? best = null;
		float bestDistSq = 48.0f * 48.0f;

		for (int i = 0; i < _racerCount; i++)
		{
			RacerState candidate = _racers[i];
			if (!candidate.Active || candidate.PlayerIndex == excludedPlayerIndex) continue;

			float dx = candidate.Position.X - origin.X;
			float dz = candidate.Position.Z - origin.Z;
			float dSq = dx * dx + dz * dz;
			if (dSq < bestDistSq)
			{
				bestDistSq = dSq;
				best = candidate;
			}
		}
		return best;
	}

	private int FindClosestWaypointIndex(Vector3 pos)
	{
		float bestDistSq = float.MaxValue;
		int bestIdx = 0;
		for (int i = 0; i < WaypointCount; i++)
		{
			float dx = pos.X - _waypoints[i].X;
			float dz = pos.Z - _waypoints[i].Y;
			float dSq = dx * dx + dz * dz;
			if (dSq < bestDistSq)
			{
				bestDistSq = dSq;
				bestIdx = i;
			}
		}
		return bestIdx;
	}

	private RacerState? FindRacerByUnit(UnitId unit)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			if (_racers[i].Unit.Value == unit.Value) return _racers[i];
		}
		return null;
	}

	private RacerState? FindRacerByPlayer(int playerIndex)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			if (_racers[i].PlayerIndex == playerIndex) return _racers[i];
		}
		return null;
	}

	private int FindRacerIndex(RacerState target)
	{
		for (int i = 0; i < _racerCount; i++)
		{
			if (ReferenceEquals(_racers[i], target)) return i;
		}
		return -1;
	}

	private static float MoveTowards(float current, float target, float maxDelta)
	{
		if (MathF.Abs(target - current) <= maxDelta) return target;
		return current + MathF.Sign(target - current) * maxDelta;
	}

	private static float WrapAngle(float radians)
	{
		while (radians > MathF.PI) radians -= MathF.PI * 2.0f;
		while (radians < -MathF.PI) radians += MathF.PI * 2.0f;
		return radians;
	}

	private static string FormatPowerUpName(PowerUpType item) => item switch
	{
		PowerUpType.TurboMushroom => "Mushroom",
		PowerUpType.GreenShell => "Green Shell",
		PowerUpType.RedShell => "Red Shell",
		PowerUpType.SpikeTrap => "Spike Trap",
		PowerUpType.LightningBolt => "Lightning",
		PowerUpType.StarPower => "Star Power",
		_ => "None"
	};
}
