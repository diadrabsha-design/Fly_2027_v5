--[[
    +----------------------------------------+
    |        A E T H E R     F L Y           |
    |            ---  By codeR  ---          |
    +----------------------------------------+
    Fly script for Roblox: PC, mobile and gamepad.

    What it is / is not
    - Client-side movement only. It needs an executor or a LocalScript that is allowed to
      control the local character. It does not bypass server checks or anti-cheat, and a game
      that validates movement on the server can still correct or kick you. Use it in
      experiences you own or are allowed to test.
    - The flight loop exists ONLY while flying (and for a fraction of a second while landing).

    Default controls
    - Fly on/off : F  (rebindable from the panel)  |  Gamepad: Y
    - Up / Down  : Space or E / LeftCtrl or Q  |  Gamepad: A or R2 / B or L2  |  UP, DOWN buttons
                   On touch devices the normal jump button also climbs.
    - Speed      : tap the SPEED text and type a number, or use = and - / the +/- buttons
                   (hold to repeat; the step grows with the speed)
    - Hide panel : RightShift

    Optional executor functions (the script works without all of them): getgenv, writefile,
    readfile, isfile. Without file functions, settings are simply not saved.
]]

local ENV = (getgenv and getgenv()) or _G

local TAG = "[AetherFly] "
local logged = {}
local function log(msg, once)
	if once then
		if logged[msg] then return end
		logged[msg] = true
	end
	warn(TAG .. msg)
end

-- one instance at a time: clean the previous run before starting
if ENV.__AetherFlyDestroy then
	local ok, err = pcall(ENV.__AetherFlyDestroy)
	if not ok then log("cleanup of the previous instance failed: " .. tostring(err)) end
	ENV.__AetherFlyDestroy = nil
end

local function boot()
	local Players = game:GetService("Players")
	local RunService = game:GetService("RunService")
	local UIS = game:GetService("UserInputService")
	local TweenService = game:GetService("TweenService")
	local HttpService = game:GetService("HttpService")
	local KC = Enum.KeyCode

	local LP = Players.LocalPlayer
	if not LP then
		log("LocalPlayer is missing: run this on the client")
		return
	end

	----------------------------------------------------------------- config
	local THEMES = {
		Color3.fromRGB(0, 229, 255),
	}

	local C = {
		Bg = Color3.new(0, 0, 0),
		Card = Color3.fromRGB(13, 13, 16),
		CardHi = Color3.fromRGB(24, 24, 29),
		Track = Color3.fromRGB(32, 32, 38),
		Text = Color3.fromRGB(238, 238, 244),
		Dim = Color3.fromRGB(128, 128, 140),
		Off = Color3.fromRGB(255, 69, 96),
		White = Color3.new(1, 1, 1),
	}

	local CFG = {
		Speed = 60,
		Min = 1,        -- lowest allowed speed
		Cap = 1000000,  -- technical ceiling: larger values only break the physics engine (NaN)
		Step = 5,       -- smallest +/- step; the real step is 5% of the speed when that is bigger
		Smooth = 10,    -- how quickly speed changes while you are giving input (higher = snappier)
		Stop = 6,       -- how quickly speed fades when you release the move keys (lower = softer)
		Turn = 18,      -- how quickly the body rotates (AlignOrientation responsiveness)
		Tilt = 0.3,     -- forward lean while moving
		Pitch = 1,      -- 0 = body stays level, 1 = body follows the camera up/down fully
		MaxPitch = 1.2, -- largest body pitch in radians (about 69 degrees)
		Brake = 7,      -- how quickly speed fades out when flight is switched off
		Theme = 1, Key = KC.F, Collapsed = false,
	}

	-- keys that already have a job here and cannot be used as the fly key
	local RESERVED = {}
	for _, k in ipairs({
		KC.W, KC.A, KC.S, KC.D, KC.Space, KC.E, KC.Q, KC.LeftControl,
		KC.Equals, KC.Minus, KC.KeypadPlus, KC.KeypadMinus,
		KC.RightShift, KC.Escape, KC.Tab, KC.Slash, KC.Return, KC.Backspace, KC.Unknown,
	}) do RESERVED[k] = true end

	local W, H_FULL, H_MIN = 236, 264, 38
	local posX, posY = nil, nil

	local function isFinite(n)
		return type(n) == "number" and n == n and n ~= math.huge and n ~= -math.huge
	end

	----------------------------------------------------------------- saved settings
	local SAVE = "AetherFly_codeR.json"
	local canFS = (typeof(writefile) == "function" and typeof(readfile) == "function" and typeof(isfile) == "function")

	local function loadSettings()
		if not canFS then return end
		local okExists, exists = pcall(isfile, SAVE)
		if not (okExists and exists) then return end
		local okRead, raw = pcall(readfile, SAVE)
		if not okRead or type(raw) ~= "string" then
			log("settings file could not be read, using defaults", true)
			return
		end
		local okJson, data = pcall(HttpService.JSONDecode, HttpService, raw)
		if not okJson or type(data) ~= "table" then
			log("settings file is corrupt, using defaults", true)
			return
		end
		if isFinite(data.Speed) then CFG.Speed = math.clamp(math.floor(data.Speed), CFG.Min, CFG.Cap) end
		if isFinite(data.Theme) and THEMES[data.Theme] then CFG.Theme = data.Theme end
		if type(data.Key) == "string" then
			local okKey, kc = pcall(function() return KC[data.Key] end)
			-- keyboard key codes are below 1000 (gamepad buttons start at 1000)
			if okKey and typeof(kc) == "EnumItem" and kc.Value < 1000 and not RESERVED[kc] then CFG.Key = kc end
		end
		if isFinite(data.X) and isFinite(data.Y) then posX, posY = data.X, data.Y end
		if type(data.Collapsed) == "boolean" then CFG.Collapsed = data.Collapsed end
	end
	loadSettings()

	----------------------------------------------------------------- state
	local conns, charConns, transient = {}, {}, {}
	local flyConn, settleConn = nil, nil
	local flying, uiUp, uiDown = false, 0, 0
	local engaged = false            -- true while we own the character (flying or landing)
	local vel = Vector3.zero
	local destroyed = false
	local collapsed = CFG.Collapsed
	local accent = THEMES[CFG.Theme]

	local cHum, cRoot = nil, nil     -- current character references
	local prevPS = nil               -- Humanoid.PlatformStand before we took over
	local lvObj, lvAtt, aoObj = nil, nil, nil -- LinearVelocity, its attachment, AlignOrientation
	local lvNextTry = 0
	local controls = nil             -- PlayerModule controls (optional)
	local held = {}                  -- keyboard keys currently down (cleared on focus loss)
	local releasers = {}             -- functions that release every held UI button
	local pads = {}                  -- connected gamepads
	local protHum, protSaved = nil, nil -- humanoid states we switched off while flying

	local heading = nil              -- last camera heading (flat unit vector), used to straighten up without spinning
	local groundK = 1                -- smoothed 0..1 factor that fades the head-down pitch near the ground

	local rayParams = RaycastParams.new()
	rayParams.FilterType = Enum.RaycastFilterType.Exclude

	local gui, main, shimmer, uiScale
	local writeNow, setFly, setUI, stopDrag, release, restoreStates
	local notify = function(_) end   -- replaced once the UI exists

	local function bind(sig, fn)
		local c = sig:Connect(fn)
		conns[#conns + 1] = c
		return c
	end

	local function isPress(i)
		return i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch
	end

	local function getChar()
		local ch = LP.Character
		if not ch then return end
		local hum = ch:FindFirstChildOfClass("Humanoid")
		local root = ch:FindFirstChild("HumanoidRootPart") or (hum and hum.RootPart)
		-- hum.RootPart can still point at a part that was removed from the character
		if hum and root and root.Parent then return ch, hum, root end
	end

	local saveQueued = false
	local function save()
		if not canFS or saveQueued or destroyed then return end
		saveQueued = true
		task.delay(1.2, function()
			saveQueued = false
			if not destroyed and writeNow then writeNow() end
		end)
	end

	----------------------------------------------------------------- teardown (defined early so a failed startup can clean up)
	local function destroy()
		if destroyed then return end
		if setFly then setFly(false, true) end
		if release then release() end
		if restoreStates then restoreStates() end
		if writeNow then writeNow() end
		destroyed = true
		if shimmer then shimmer:Cancel() end
		if stopDrag then stopDrag() end
		for _, c in ipairs(charConns) do c:Disconnect() end
		table.clear(charConns)
		for c in pairs(transient) do c:Disconnect() end
		table.clear(transient)
		for _, c in ipairs(conns) do c:Disconnect() end
		table.clear(conns)
		if gui then gui:Destroy() end
		if ENV.__AetherFlyDestroy == destroy then ENV.__AetherFlyDestroy = nil end
	end
	ENV.__AetherFlyDestroy = destroy

	----------------------------------------------------------------- input helpers
	-- PlayerModule gives keyboard, touch stick and gamepad stick in one vector. Optional.
	task.spawn(function()
		local ok, result = pcall(function()
			local ps = LP:WaitForChild("PlayerScripts", 10)
			local pm = ps and ps:WaitForChild("PlayerModule", 10)
			return pm and require(pm):GetControls()
		end)
		if destroyed then return end
		if ok and result then
			controls = result
		else
			log("PlayerModule controls not available, using Humanoid.MoveDirection (horizontal only)", true)
		end
	end)

	-- world-space move direction; forward/back follows the camera pitch (look up + W = climb)
	local function getMove(hum, cam)
		if controls then
			local ok, v = pcall(controls.GetMoveVector, controls)
			if ok and typeof(v) == "Vector3" then
				local flatV = Vector3.new(v.X, 0, v.Z) -- vertical comes only from our own up/down input
				if flatV.Magnitude > 0.001 then return cam.CFrame:VectorToWorldSpace(flatV) end
			else
				log("PlayerModule controls stopped responding, using Humanoid.MoveDirection", true)
				controls = nil
			end
		end
		local md = hum.MoveDirection
		if md.Magnitude > 0.01 then return md end
		return Vector3.zero
	end

	local function refreshPads()
		local ok, list = pcall(UIS.GetConnectedGamepads, UIS)
		pads = (ok and type(list) == "table") and list or {}
	end
	refreshPads()
	bind(UIS.GamepadConnected, refreshPads)
	bind(UIS.GamepadDisconnected, refreshPads)

	-- UP and DOWN buttons are summed on purpose: pressing both cancels out
	local function verticalInput(hum)
		local up = uiUp - uiDown
		if not UIS:GetFocusedTextBox() then
			if held[KC.Space] or held[KC.E] then up = up + 1 end
			if held[KC.LeftControl] or held[KC.Q] then up = up - 1 end
		end
		-- on touch devices the normal jump button climbs too
		if UIS.TouchEnabled and hum and hum.Jump then up = up + 1 end
		for _, pad in ipairs(pads) do
			if UIS:IsGamepadButtonDown(pad, KC.ButtonA) or UIS:IsGamepadButtonDown(pad, KC.ButtonR2) then up = up + 1 end
			if UIS:IsGamepadButtonDown(pad, KC.ButtonB) or UIS:IsGamepadButtonDown(pad, KC.ButtonL2) then up = up - 1 end
		end
		return math.clamp(up, -1, 1)
	end

	----------------------------------------------------------------- fly core
	local PROTECT = { Enum.HumanoidStateType.FallingDown, Enum.HumanoidStateType.Ragdoll }

	-- while flying (and shortly after) the humanoid must not fall over or ragdoll after a bump
	local function protectStates(hum)
		if protHum == hum then return end
		if protHum then restoreStates() end
		protHum, protSaved = hum, {}
		for _, st in ipairs(PROTECT) do
			pcall(function()
				protSaved[st] = hum:GetStateEnabled(st)
				hum:SetStateEnabled(st, false)
			end)
		end
	end

	restoreStates = function()
		local hum, saved = protHum, protSaved
		protHum, protSaved = nil, nil
		if not (hum and saved and hum.Parent) then return end
		for st, was in pairs(saved) do
			pcall(function() hum:SetStateEnabled(st, was) end)
		end
	end

	-- finite limits: an unlimited force makes collisions violent (shaking, being thrown around)
	local function forceLimit(root)
		return math.max(root.AssemblyMass, 1) * math.max(1200, CFG.Speed * CFG.Smooth * 2)
	end

	local function removeLV()
		if aoObj then aoObj:Destroy() aoObj = nil end
		if lvObj then lvObj:Destroy() lvObj = nil end
		if lvAtt then lvAtt:Destroy() lvAtt = nil end
	end

	-- A LinearVelocity constraint holds the target velocity inside the physics solver, so
	-- gravity is overridden whatever the frame time. An AlignOrientation constraint rotates
	-- the body smoothly (no per-frame CFrame writes). If either cannot be created the code
	-- falls back to direct velocity / CFrame updates.
	local function makeLV(root)
		removeLV()
		rayParams.FilterDescendantsInstances = { root.Parent }
		local ok, err = pcall(function()
			local att = Instance.new("Attachment")
			att.Name = "AetherFly_Att"
			-- The push must go through the center of mass. Applied at the root part (which is not
			-- the center of mass) every speed change also creates a torque, and that torque is
			-- what swung the legs forward/back whenever the speed dropped.
			att.Position = root.CFrame:PointToObjectSpace(root.AssemblyCenterOfMass)
			att.Parent = root
			lvAtt = att
			local lv = Instance.new("LinearVelocity")
			lv.Name = "AetherFly_LV"
			lv.Attachment0 = att
			lv.RelativeTo = Enum.ActuatorRelativeTo.World
			lv.VelocityConstraintMode = Enum.VelocityConstraintMode.Vector
			lv.MaxForce = forceLimit(root)
			lv.VectorVelocity = Vector3.zero
			lv.Parent = root
			lvObj = lv
		end)
		if not ok then
			removeLV()
			log("could not create LinearVelocity (" .. tostring(err) .. "), using direct velocity", true)
			notify("Fallback physics mode")
			return false
		end
		if lvAtt then
			local okAO = pcall(function()
				local ao = Instance.new("AlignOrientation")
				ao.Name = "AetherFly_AO"
				ao.Mode = Enum.OrientationAlignmentMode.OneAttachment
				ao.Attachment0 = lvAtt
				ao.RigidityEnabled = false
				ao.MaxTorque = math.max(root.AssemblyMass, 1) * 3000
				ao.MaxAngularVelocity = 14
				ao.Responsiveness = CFG.Turn
				ao.CFrame = root.CFrame - root.CFrame.Position
				ao.Parent = root
				aoObj = ao
			end)
			if not okAO then
				if aoObj then aoObj:Destroy() aoObj = nil end
				log("could not create AlignOrientation, using direct rotation", true)
			end
		end
		return true
	end

	-- an upright version of the root's current orientation (keeps the heading)
	local function uprightCFrame(root)
		-- the stored heading is stable; re-deriving it from a tilted body gets noisy near vertical
		local flat = heading
		if not flat then
			local look = root.CFrame.LookVector
			flat = Vector3.new(look.X, 0, look.Z)
			if flat.Magnitude < 0.05 then
				local cam = workspace.CurrentCamera
				if cam then
					local l = cam.CFrame.LookVector
					flat = Vector3.new(l.X, 0, l.Z)
				end
			end
			if flat.Magnitude < 0.01 then flat = Vector3.new(0, 0, -1) end
			flat = flat.Unit
		end
		local p = root.Position
		return CFrame.lookAt(p, p + flat)
	end

	-- orientation while flying: heading AND pitch follow the camera, plus a forward lean
	local function aimCFrame(root, cam, dt)
		local look = cam.CFrame.LookVector
		local flat = Vector3.new(look.X, 0, look.Z)
		if flat.Magnitude < 0.01 then return nil end -- looking straight up/down: keep the heading
		flat = flat.Unit
		heading = flat
		local pitch = math.asin(math.clamp(look.Y, -1, 1)) * CFG.Pitch
		if CFG.Tilt > 0 then
			local lean = math.clamp(vel:Dot(flat) / CFG.Speed, -1, 1) * CFG.Tilt
			pitch = pitch - lean
		end
		pitch = math.clamp(pitch, -CFG.MaxPitch, CFG.MaxPitch)
		-- near the ground the head-down pitch fades out, so the face never digs into the floor.
		-- The factor is smoothed, otherwise flying fast over uneven ground makes the body twitch.
		local want = 1
		if pitch < 0 then
			local hit = workspace:Raycast(root.Position, Vector3.new(0, -12, 0), rayParams)
			if hit then
				local d = root.Position.Y - hit.Position.Y
				want = math.clamp((d - 3.5) / 6, 0, 1)
			end
		end
		groundK = groundK + (want - groundK) * (1 - math.exp(-dt * 8))
		if pitch < 0 then pitch = pitch * groundK end
		local dir = flat * math.cos(pitch) + Vector3.new(0, math.sin(pitch), 0)
		local p = root.Position
		return CFrame.lookAt(p, p + dir)
	end

	local function applyMotion(root, dt, target)
		if lvObj and lvObj.Parent == root then
			lvObj.VectorVelocity = vel
			lvObj.MaxForce = forceLimit(root)
			if lvAtt and lvAtt.Parent == root then
				lvAtt.Position = root.CFrame:PointToObjectSpace(root.AssemblyCenterOfMass)
			end
		else
			-- fallback: set the velocity directly with a one-step gravity offset
			root.AssemblyLinearVelocity = vel + Vector3.new(0, workspace.Gravity * dt, 0)
		end
		if not target then return end
		if aoObj and aoObj.Parent == root then
			aoObj.CFrame = target
		else
			root.AssemblyAngularVelocity = Vector3.zero
			root.CFrame = root.CFrame:Lerp(target, 1 - math.exp(-dt * CFG.Turn))
		end
	end

	local function step(dt)
		if dt > 0.1 then dt = 0.1 end

		local hum, root = cHum, cRoot
		if not (hum and root and hum.Parent and root.Parent) then
			local _, h, r = getChar()
			if not (h and r) then
				setFly(false, true)
				notify("Character lost")
				return
			end
			cHum, cRoot = h, r
			hum, root = h, r
			makeLV(root)
		end
		if hum.Health <= 0 then setFly(false, true) return end
		if hum.SeatPart then
			setFly(false, true)
			notify("Seated: flight stopped")
			return
		end
		if not hum.PlatformStand then hum.PlatformStand = true end

		local cam = workspace.CurrentCamera
		if not cam then return end

		-- the game (or a respawn) may have removed our constraints: rebuild them, at most once a second
		if not (lvObj and lvObj.Parent == root) then
			local now = os.clock()
			if now >= lvNextTry then
				lvNextTry = now + 1
				makeLV(root)
			end
		end

		-- blocked by something: follow the real velocity instead of building up a push into it
		local actual = root.AssemblyLinearVelocity
		if vel.Magnitude > 4 and (actual - vel).Magnitude > math.max(10, CFG.Speed * 0.4) then
			vel = vel:Lerp(actual, 0.6)
		end

		local dir = getMove(hum, cam) + Vector3.new(0, verticalInput(hum), 0)
		if dir.Magnitude > 1 then dir = dir.Unit end -- equal speed in every direction, diagonals included

		-- releasing the keys fades the speed out more gently than it builds up, so a stop
		-- from a very high speed is not a sudden jerk
		local rate = (dir.Magnitude > 0.02) and CFG.Smooth or CFG.Stop
		vel = vel:Lerp(dir * CFG.Speed, 1 - math.exp(-dt * rate))
		applyMotion(root, dt, aimCFrame(root, cam, dt))
	end

	-- Final hand-back of the character. Always safe to call, more than once.
	release = function()
		if settleConn then settleConn:Disconnect() settleConn = nil end
		if flyConn then flyConn:Disconnect() flyConn = nil end
		flying = false
		removeLV()
		vel = Vector3.zero
		if not engaged then return end
		engaged = false

		local hum, root = cHum, cRoot
		local seated = hum and hum.SeatPart ~= nil
		-- never touch the root of a seated character: it is welded to the vehicle
		if root and root.Parent and not seated then
			root.AssemblyLinearVelocity = Vector3.zero
			root.AssemblyAngularVelocity = Vector3.zero
			-- only a small correction is applied directly; a big one could push the body into the floor
			if root.CFrame.UpVector.Y > 0.9 then root.CFrame = uprightCFrame(root) end
		end
		if hum and hum.Parent then
			local was = (prevPS == true)
			prevPS = nil
			hum.PlatformStand = was -- give back whatever the game had
			if hum.Health > 0 and not was and not seated then
				pcall(function() hum:ChangeState(Enum.HumanoidStateType.Freefall) end)
			end
		end
		-- keep the fall-over protection for a moment, so the landing cannot ragdoll the character
		task.delay(1.5, function()
			if not engaged then restoreStates() end
		end)
	end

	-- Soft landing: the speed fades out and the body straightens up while the physics
	-- constraints are still active, then control goes back to the game.
	local function beginSettle(hum, root)
		local t0 = os.clock()
		settleConn = RunService.Heartbeat:Connect(function(dt)
			if dt > 0.1 then dt = 0.1 end
			if destroyed or not (hum.Parent and root.Parent) or hum.Health <= 0 or hum.SeatPart then
				release()
				return
			end
			vel = vel:Lerp(Vector3.zero, 1 - math.exp(-dt * CFG.Brake))
			applyMotion(root, dt, uprightCFrame(root))
			local elapsed = os.clock() - t0
			local upright = root.CFrame.UpVector.Y > 0.995
			if elapsed >= 0.9 or (elapsed >= 0.15 and vel.Magnitude < 2 and upright) then
				release()
			end
		end)
	end

	setFly = function(on, instant)
		if destroyed then return end
		if on then
			if flying then return end
			local _, hum, root = getChar()
			if not (hum and root) then notify("No character yet") return end
			if hum.Health <= 0 then notify("Character is dead") return end
			if hum.SeatPart then notify("Stand up first") return end
			local resume = (settleConn ~= nil and engaged and cHum == hum and cRoot == root)
			if settleConn then settleConn:Disconnect() settleConn = nil end
			if not resume then
				release()
				cHum, cRoot = hum, root
				vel = Vector3.zero
				heading, groundK = nil, 1
				prevPS = hum.PlatformStand
				protectStates(hum)
				hum.PlatformStand = true
				engaged = true
				makeLV(root)
			end
			flying = true
			flyConn = RunService.Heartbeat:Connect(step)
		else
			if not flying then return end
			flying = false
			if flyConn then flyConn:Disconnect() flyConn = nil end
			local hum, root = cHum, cRoot
			local canSettle = (not instant) and engaged and hum and root and hum.Parent and root.Parent
				and hum.Health > 0 and not hum.SeatPart
			if canSettle then
				beginSettle(hum, root)
			else
				release()
			end
		end
		if setUI then setUI() end
	end

	----------------------------------------------------------------- UI helpers
	local function new(class, props, parent)
		local o = Instance.new(class)
		-- Roblox can auto-translate UI text to the player's language (that is where
		-- Arabic words such as UP / DOWN translations come from); keep the text English
		if o:IsA("GuiBase2d") then pcall(function() o.AutoLocalize = false end) end
		for k, v in pairs(props) do o[k] = v end
		if parent then o.Parent = parent end
		return o
	end

	local function tween(o, props, t, style)
		TweenService:Create(o, TweenInfo.new(t or 0.16, style or Enum.EasingStyle.Quad, Enum.EasingDirection.Out), props):Play()
	end

	local function round(o, r) new("UICorner", { CornerRadius = UDim.new(0, r) }, o) end

	local themed = {}
	local function onTheme(fn)
		themed[#themed + 1] = fn
		fn()
	end

	gui = new("ScreenGui", {
		Name = "AetherFly", ResetOnSpawn = false, IgnoreGuiInset = true,
		ZIndexBehavior = Enum.ZIndexBehavior.Sibling, DisplayOrder = 999,
	})
	-- keep the panel clear of phone notches and rounded corners (property is missing on old clients)
	pcall(function() gui.ScreenInsets = Enum.ScreenInsets.DeviceSafeInsets end)

	local function mount()
		local candidates = {
			function() return LP:FindFirstChildOfClass("PlayerGui") or LP:WaitForChild("PlayerGui", 5) end,
			function() return game:GetService("CoreGui") end,
		}
		for _, get in ipairs(candidates) do
			local ok, parent = pcall(get)
			if ok and parent then
				local ok2 = pcall(function() gui.Parent = parent end)
				if ok2 and gui.Parent == parent then return true end
			end
		end
		return false
	end
	if not mount() then
		error("no place to attach the interface (PlayerGui and CoreGui are both unavailable)")
	end

	-- if the game deletes the interface, stop everything instead of flying with no way to turn it off
	bind(gui.AncestryChanged, function(_, parent)
		if not parent and not destroyed then
			log("the interface was removed, shutting down")
			destroy()
		end
	end)

	local function viewport()
		local a = gui.AbsoluteSize
		if a.X > 10 and a.Y > 10 then return a end
		local cam = workspace.CurrentCamera
		local v = cam and cam.ViewportSize
		if v and v.X > 10 and v.Y > 10 then return v end
		return Vector2.new(1280, 720)
	end

	local function computeScale()
		local vp = viewport()
		return math.clamp(math.min((vp.Y - 16) / H_FULL, (vp.X - 16) / W, 1), 0.55, 1)
	end

	-- free placement: the panel may go partly off screen, but a small part always stays visible
	local function clampPos(x, y)
		local vp = viewport()
		local s = uiScale and uiScale.Scale or 1
		local minX = -(W * s) + 110 -- keeps the collapse and close buttons visible
		local maxX = vp.X - 60      -- keeps part of the title visible
		return math.clamp(x, minX, maxX), math.clamp(y, 0, math.max(0, vp.Y - 40))
	end

	----------------------------------------------------------------- UI build
	main = new("Frame", {
		Size = UDim2.fromOffset(W, collapsed and H_MIN or H_FULL),
		BackgroundColor3 = C.Bg, BorderSizePixel = 0, ClipsDescendants = true,
		Active = true, -- clicks on the panel never reach the game
	}, gui)
	round(main, 14)
	new("UIStroke", { Color = C.White, Transparency = 0.88, Thickness = 1 }, main)
	uiScale = new("UIScale", { Scale = computeScale() }, main)

	if not (isFinite(posX) and isFinite(posY)) then
		local vp, s = viewport(), uiScale.Scale
		if UIS.TouchEnabled and not UIS.KeyboardEnabled then
			posX, posY = vp.X - W * s - 12, 12 -- top-right keeps clear of the thumbstick and jump button
		else
			posX, posY = 24, (vp.Y - H_FULL * s) / 2
		end
	end
	posX, posY = clampPos(posX, posY)
	main.Position = UDim2.fromOffset(posX, posY)

	local bar = new("Frame", { Size = UDim2.new(1, 0, 0, H_MIN), BackgroundTransparency = 1, Active = true }, main)
	local titleLabel = new("TextLabel", {
		BackgroundTransparency = 1, Position = UDim2.fromOffset(14, 0), Size = UDim2.new(1, -90, 1, 0),
		Text = "codeR", Font = Enum.Font.GothamBold, TextSize = 13,
		TextColor3 = C.Text, TextXAlignment = Enum.TextXAlignment.Left,
		TextTruncate = Enum.TextTruncate.AtEnd,
	}, bar)

	-- short status / error message shown in the title for a moment (no extra space needed)
	local titleToken = 0
	notify = function(msg)
		if destroyed then return end
		titleToken = titleToken + 1
		local my = titleToken
		titleLabel.Text = msg
		titleLabel.TextColor3 = C.Off
		task.delay(3, function()
			if my == titleToken and not destroyed then
				titleLabel.Text = "codeR"
				titleLabel.TextColor3 = C.Text
			end
		end)
	end

	local function iconBtn(txt, x)
		local b = new("TextButton", {
			Size = UDim2.fromOffset(30, 30), Position = UDim2.new(1, x, 0.5, -15),
			BackgroundColor3 = C.Card, Text = txt, Font = Enum.Font.GothamBold, TextSize = 14,
			TextColor3 = C.Dim, AutoButtonColor = false, Selectable = false,
		}, bar)
		round(b, 8)
		bind(b.MouseEnter, function() tween(b, { TextColor3 = C.Text }) end)
		bind(b.MouseLeave, function() tween(b, { TextColor3 = C.Dim }) end)
		return b
	end
	local btnMin = iconBtn(collapsed and "+" or "-", -72)
	local btnClose = iconBtn("x", -38)

	local body = new("Frame", {
		Position = UDim2.fromOffset(0, H_MIN), Size = UDim2.new(1, 0, 1, -H_MIN),
		BackgroundTransparency = 1, Visible = not collapsed,
	}, main)
	new("UIPadding", { PaddingLeft = UDim.new(0, 12), PaddingRight = UDim.new(0, 12) }, body)

	-- press tracking shared by every hold button: follows ONE input object, so a finger that
	-- slides off the button keeps holding, and a release anywhere ends the press.
	local function trackPress(obj, onDown, onUp)
		local active = nil
		local function releasePress()
			if active then
				active = nil
				onUp()
			end
		end
		bind(obj.InputBegan, function(i)
			if not isPress(i) or active then return end
			active = i
			onDown()
			local c
			c = i.Changed:Connect(function()
				if i.UserInputState == Enum.UserInputState.End then
					c:Disconnect()
					transient[c] = nil
					if active == i then releasePress() end
				end
			end)
			transient[c] = true
		end)
		bind(obj.MouseLeave, function()
			-- only a mouse stops when it leaves the button
			if active and active.UserInputType == Enum.UserInputType.MouseButton1 then releasePress() end
		end)
		releasers[#releasers + 1] = releasePress
	end

	-- main toggle
	local toggle = new("TextButton", {
		Size = UDim2.new(1, 0, 0, 44), BackgroundColor3 = C.Card, AutoButtonColor = false,
		Text = "", BorderSizePixel = 0, Selectable = false,
	}, body)
	round(toggle, 12)
	local tStroke = new("UIStroke", { Color = C.Off, Transparency = 0.45, Thickness = 1.5 }, toggle)
	local dot = new("Frame", {
		Size = UDim2.fromOffset(10, 10), Position = UDim2.new(0, 16, 0.5, -5),
		BackgroundColor3 = C.Off, BorderSizePixel = 0,
	}, toggle)
	round(dot, 5)
	local tLabel = new("TextLabel", {
		BackgroundTransparency = 1, Position = UDim2.fromOffset(36, 0), Size = UDim2.new(1, -46, 1, 0),
		Text = "FLY  OFF", Font = Enum.Font.GothamBold, TextSize = 14, TextColor3 = C.Text,
		TextXAlignment = Enum.TextXAlignment.Left,
	}, toggle)

	-- speed row
	local speedRow = new("Frame", {
		Position = UDim2.fromOffset(0, 54), Size = UDim2.new(1, 0, 0, 44), BackgroundColor3 = C.Card, BorderSizePixel = 0,
	}, body)
	round(speedRow, 12)

	-- the dimmed SPEED text is an input box: tap it and type any number
	local speedBox = new("TextBox", {
		BackgroundTransparency = 1, Position = UDim2.fromOffset(44, 2), Size = UDim2.new(1, -88, 0, 30),
		Text = "SPEED  60", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.Dim,
		ClearTextOnFocus = true, TextEditable = true, TextTruncate = Enum.TextTruncate.AtEnd,
	}, speedRow)
	local track = new("Frame", {
		Position = UDim2.new(0, 48, 0, 35), Size = UDim2.new(1, -96, 0, 3),
		BackgroundColor3 = C.Track, BorderSizePixel = 0,
	}, speedRow)
	round(track, 2)
	local fill = new("Frame", { Size = UDim2.new(0.3, 0, 1, 0), BorderSizePixel = 0 }, track)
	round(fill, 2)

	local function refreshSpeed()
		if not speedBox:IsFocused() then
			speedBox.Text = "SPEED  " .. CFG.Speed
		end
		-- the bar has no end: it approaches full as the speed grows
		fill.Size = UDim2.new(CFG.Speed / (CFG.Speed + 100), 0, 1, 0)
	end

	local function setSpeed(v)
		if not isFinite(v) then return end
		local n = math.clamp(math.floor(v + 0.5), CFG.Min, CFG.Cap)
		if n == CFG.Speed then return end
		CFG.Speed = n
		refreshSpeed()
		save()
	end

	-- the +/- step grows with the speed, so high values can be reached quickly
	local function stepFor(speed)
		return math.max(CFG.Step, math.floor(speed * 0.05))
	end

	bind(speedBox.Focused, function()
		speedBox.TextColor3 = C.Text
	end)
	bind(speedBox.FocusLost, function()
		speedBox.TextColor3 = C.Dim
		local digits = string.gsub(speedBox.Text, "[^%d%.]", "")
		local n = tonumber(digits)
		if n then setSpeed(n) end
		refreshSpeed()
	end)

	local function stepBtn(txt, pos, sign)
		local b = new("TextButton", {
			Size = UDim2.fromOffset(44, 44), Position = pos, BackgroundTransparency = 1,
			Text = txt, Font = Enum.Font.GothamBold, TextSize = 20, TextColor3 = accent,
			AutoButtonColor = false, Selectable = false,
		}, speedRow)
		onTheme(function() b.TextColor3 = accent end)
		local token = 0
		trackPress(b, function()
			token = token + 1
			local my = token
			setSpeed(CFG.Speed + sign * stepFor(CFG.Speed))
			task.spawn(function() -- hold to repeat
				task.wait(0.35)
				while token == my and not destroyed do
					setSpeed(CFG.Speed + sign * stepFor(CFG.Speed))
					task.wait(0.06)
				end
			end)
		end, function() token = token + 1 end)
	end
	stepBtn("-", UDim2.fromOffset(0, 0), -1)
	stepBtn("+", UDim2.new(1, -44, 0, 0), 1)

	-- up / down (touch and no-keyboard friendly)
	local function holdBtn(txt, xScale, onChange)
		local b = new("TextButton", {
			Position = UDim2.new(xScale, xScale == 0 and 0 or 3, 0, 106), Size = UDim2.new(0.5, -3, 0, 38),
			BackgroundColor3 = C.Card, Text = txt, Font = Enum.Font.GothamBold, TextSize = 12,
			TextColor3 = C.Dim, AutoButtonColor = false, Selectable = false,
		}, body)
		round(b, 10)
		trackPress(b, function()
			onChange(1)
			tween(b, { TextColor3 = accent, BackgroundColor3 = C.CardHi }, 0.1)
		end, function()
			onChange(0)
			tween(b, { TextColor3 = C.Dim, BackgroundColor3 = C.Card }, 0.1)
		end)
	end
	holdBtn("UP", 0, function(v) uiUp = v end)
	holdBtn("DOWN", 0.5, function(v) uiDown = v end)

	-- settings row: rebindable key
	local keyChip = new("TextButton", {
		Position = UDim2.fromOffset(0, 154), Size = UDim2.fromOffset(78, 24), BackgroundColor3 = C.Card,
		Text = "", Font = Enum.Font.GothamBold, TextSize = 10, TextColor3 = C.Dim,
		AutoButtonColor = false, Selectable = false,
	}, body)
	round(keyChip, 8)

	local function keyText()
		return string.upper(string.sub(CFG.Key.Name, 1, 8))
	end
	local function refreshKey()
		keyChip.Text = "KEY  " .. keyText()
	end
	refreshKey()

	local swatches = {}

	-- logo: By codeR
	local logo = new("Frame", {
		Position = UDim2.fromOffset(0, 186), Size = UDim2.new(1, 0, 0, 30), BackgroundTransparency = 1,
	}, body)
	local row = new("Frame", {
		AnchorPoint = Vector2.new(0.5, 0.5), Position = UDim2.fromScale(0.5, 0.5),
		Size = UDim2.fromOffset(0, 24), AutomaticSize = Enum.AutomaticSize.X, BackgroundTransparency = 1,
	}, logo)
	new("UIListLayout", {
		FillDirection = Enum.FillDirection.Horizontal, HorizontalAlignment = Enum.HorizontalAlignment.Center,
		VerticalAlignment = Enum.VerticalAlignment.Center, SortOrder = Enum.SortOrder.LayoutOrder,
		Padding = UDim.new(0, 7),
	}, row)

	local function logoLine(order, fadeIn)
		local l = new("Frame", {
			LayoutOrder = order, Size = UDim2.fromOffset(28, 1), BackgroundColor3 = C.White, BorderSizePixel = 0,
		}, row)
		local g = new("UIGradient", {
			Transparency = NumberSequence.new({
				NumberSequenceKeypoint.new(0, fadeIn and 1 or 0.1),
				NumberSequenceKeypoint.new(1, fadeIn and 0.1 or 1),
			}),
		}, l)
		onTheme(function() g.Color = ColorSequence.new(accent) end)
	end
	local function logoDiamond(order)
		local d = new("Frame", {
			LayoutOrder = order, Size = UDim2.fromOffset(6, 6), Rotation = 45, BorderSizePixel = 0,
		}, row)
		onTheme(function() d.BackgroundColor3 = accent end)
	end

	logoLine(1, true)
	logoDiamond(2)
	new("TextLabel", {
		LayoutOrder = 3, BackgroundTransparency = 1, Size = UDim2.fromOffset(0, 24), AutomaticSize = Enum.AutomaticSize.X,
		Text = "By", Font = Enum.Font.GothamMedium, TextSize = 11, TextColor3 = C.Dim,
	}, row)
	local codeR = new("TextLabel", {
		LayoutOrder = 4, BackgroundTransparency = 1, Size = UDim2.fromOffset(0, 24), AutomaticSize = Enum.AutomaticSize.X,
		Text = "codeR", Font = Enum.Font.GothamBlack, TextSize = 17, TextColor3 = C.White,
	}, row)
	local glow = new("UIStroke", { Thickness = 1, Transparency = 0.6 }, codeR)
	local shine = new("UIGradient", { Offset = Vector2.new(-1, 0) }, codeR)
	onTheme(function()
		glow.Color = accent
		shine.Color = ColorSequence.new({
			ColorSequenceKeypoint.new(0, accent),
			ColorSequenceKeypoint.new(0.42, accent),
			ColorSequenceKeypoint.new(0.5, C.White),
			ColorSequenceKeypoint.new(0.58, accent),
			ColorSequenceKeypoint.new(1, accent),
		})
		for idx, st in ipairs(swatches) do st.Transparency = (idx == CFG.Theme) and 0 or 1 end
	end)
	logoDiamond(5)
	logoLine(6, false)

	-- a single light sweep (no endless animation, so the idle panel costs nothing)
	shimmer = TweenService:Create(shine, TweenInfo.new(1.6, Enum.EasingStyle.Sine, Enum.EasingDirection.InOut),
		{ Offset = Vector2.new(1, 0) })
	local function playShimmer()
		if destroyed or collapsed or not main.Visible then return end
		shine.Offset = Vector2.new(-1, 0)
		shimmer:Play()
	end

	----------------------------------------------------------------- UI state
	setUI = function()
		local col = flying and accent or C.Off
		tween(dot, { BackgroundColor3 = col })
		tween(tStroke, { Color = col })
		tLabel.Text = flying and "FLY  ON" or "FLY  OFF"
		fill.BackgroundColor3 = accent
	end
	refreshSpeed()
	onTheme(function() fill.BackgroundColor3 = accent end)
	setUI()

	bind(toggle.Activated, function() setFly(not flying) end)
	bind(toggle.MouseEnter, function() tween(toggle, { BackgroundColor3 = C.CardHi }) end)
	bind(toggle.MouseLeave, function() tween(toggle, { BackgroundColor3 = C.Card }) end)

	----------------------------------------------------------------- layout, collapse, drag
	local function relayout()
		uiScale.Scale = computeScale()
		posX, posY = clampPos(posX, posY)
		main.Position = UDim2.fromOffset(posX, posY)
	end
	bind(gui:GetPropertyChangedSignal("AbsoluteSize"), relayout)

	local collapseToken = 0
	local function setCollapsed(v)
		collapsed = v
		btnMin.Text = v and "+" or "-"
		collapseToken = collapseToken + 1
		local my = collapseToken
		if not v then body.Visible = true end
		posX, posY = clampPos(posX, posY)
		tween(main, {
			Size = UDim2.fromOffset(W, v and H_MIN or H_FULL),
			Position = UDim2.fromOffset(posX, posY),
		}, 0.22)
		if v then
			task.delay(0.25, function()
				if collapseToken == my and collapsed and not destroyed then body.Visible = false end
			end)
		else
			playShimmer()
		end
		save()
	end
	bind(btnMin.Activated, function() setCollapsed(not collapsed) end)

	-- drag connections exist only while dragging
	local dragMove, dragEnd = nil, nil
	stopDrag = function()
		if dragMove then dragMove:Disconnect() dragMove = nil end
		if dragEnd then dragEnd:Disconnect() dragEnd = nil end
		save()
	end

	bind(bar.InputBegan, function(i)
		if not isPress(i) or dragMove then return end
		local startX, startY = posX, posY
		local mx, my = i.Position.X, i.Position.Y
		dragMove = UIS.InputChanged:Connect(function(m)
			if m.UserInputType == Enum.UserInputType.MouseMovement or m == i then
				posX, posY = clampPos(startX + (m.Position.X - mx), startY + (m.Position.Y - my))
				main.Position = UDim2.fromOffset(posX, posY)
			end
		end)
		dragEnd = i.Changed:Connect(function()
			if i.UserInputState == Enum.UserInputState.End then stopDrag() end
		end)
	end)

	----------------------------------------------------------------- key rebinding + shortcuts
	local listening, listenToken = false, 0
	local function stopListening()
		listening = false
		listenToken = listenToken + 1
		refreshKey()
		tween(keyChip, { TextColor3 = C.Dim })
	end

	bind(keyChip.Activated, function()
		if listening then stopListening() return end
		listening = true
		listenToken = listenToken + 1
		local my = listenToken
		keyChip.Text = "PRESS KEY"
		tween(keyChip, { TextColor3 = accent })
		task.delay(5, function()
			if listening and listenToken == my and not destroyed then stopListening() end
		end)
	end)

	local function releaseAll()
		for _, r in ipairs(releasers) do r() end
		table.clear(held)
		uiUp, uiDown = 0, 0
	end

	bind(UIS.InputBegan, function(i, gp)
		if i.UserInputType == Enum.UserInputType.Keyboard then
			local k = i.KeyCode
			held[k] = true
			if UIS:GetFocusedTextBox() then return end
			if listening then
				if k == KC.Escape then
					stopListening()
				elseif RESERVED[k] then
					notify("Key already in use")
				else
					CFG.Key = k
					stopListening()
					save()
				end
				return
			end
			if k == CFG.Key then
				setFly(not flying)
			elseif k == KC.Equals or k == KC.KeypadPlus then
				setSpeed(CFG.Speed + stepFor(CFG.Speed))
			elseif k == KC.Minus or k == KC.KeypadMinus then
				setSpeed(CFG.Speed - stepFor(CFG.Speed))
			elseif k == KC.RightShift and not gp then
				main.Visible = not main.Visible
				playShimmer()
			end
		elseif i.KeyCode == KC.ButtonY and not gp then
			setFly(not flying)
		end
	end)
	bind(UIS.InputEnded, function(i)
		if i.UserInputType == Enum.UserInputType.Keyboard then held[i.KeyCode] = nil end
	end)
	-- a key released while the window was unfocused is never reported, so forget everything held
	bind(UIS.WindowFocusReleased, releaseAll)

	----------------------------------------------------------------- character lifecycle
	local function onChar(ch)
		for _, c in ipairs(charConns) do c:Disconnect() end
		table.clear(charConns)
		release()
		cHum, cRoot = nil, nil
		uiUp, uiDown = 0, 0
		setUI()
		local hum = ch:WaitForChild("Humanoid", 10)
		local root = ch:WaitForChild("HumanoidRootPart", 10)
		if destroyed or LP.Character ~= ch then return end
		if not (hum and root) then
			log("this character has no Humanoid / HumanoidRootPart (custom rig), flight is unavailable", true)
			notify("Unsupported character rig")
			return
		end
		cHum, cRoot = hum, root
		charConns[#charConns + 1] = hum.Died:Connect(function() setFly(false, true) end)
	end

	bind(LP.CharacterAdded, function(ch) task.spawn(onChar, ch) end)
	bind(LP.CharacterRemoving, function() setFly(false, true) end)
	if LP.Character then task.spawn(onChar, LP.Character) end

	----------------------------------------------------------------- settings writer + close
	writeNow = function()
		if not canFS then return end
		local data = {
			Speed = CFG.Speed, Theme = CFG.Theme, Key = CFG.Key.Name,
			X = isFinite(posX) and posX or nil, Y = isFinite(posY) and posY or nil, Collapsed = collapsed,
		}
		local ok, err = pcall(function() writefile(SAVE, HttpService:JSONEncode(data)) end)
		if not ok then log("could not save settings: " .. tostring(err), true) end
	end

	bind(btnClose.Activated, destroy)
	playShimmer()
end

local ok, err = xpcall(boot, function(e) return debug.traceback(tostring(e), 2) end)
if not ok then
	warn(TAG .. "startup failed, cleaning up:\n" .. tostring(err))
	if ENV.__AetherFlyDestroy then pcall(ENV.__AetherFlyDestroy) end
end
