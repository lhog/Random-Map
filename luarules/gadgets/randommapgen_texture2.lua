--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
if (gadgetHandler:IsSyncedCode()) then
	return
end
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

function gadget:GetInfo()
	return {
		name      = "Unified Texturing2",
		desc      = "Applies basic textures on maps based on slopemap",
		author    = "Google Frog (edited for randommapgen purposes by Doo)",
		date      = "25 June 2012, edited 2018", --24 August 2013
		license   = "GNU GPL, v2 or later",
		layer     = 10,
		enabled   = true, --  loaded by default?
	}
end

-----------------------------------------------------------------
-- Runtime constants and variables
-----------------------------------------------------------------

local MAP_X = Game.mapSizeX
local MAP_Z = Game.mapSizeZ

local BLOCK_SIZE  = 8
local SPLAT_BLOCK_SIZE = 4 --arbitrary
local SQUARE_SIZE = 1024

local SQUARES_X = MAP_X/SQUARE_SIZE
local SQUARES_Z = MAP_Z/SQUARE_SIZE

local SPLAT_X = MAP_X/SPLAT_BLOCK_SIZE
local SPLAT_Z = MAP_Z/SPLAT_BLOCK_SIZE

local VEH_NORMAL     = 0.892
local BOT_NORMAL     = 0.585
local SHALLOW_HEIGHT = -22

local USE_SHADING_TEXTURE = (Spring.GetConfigInt("AdvMapShading") == 1)

local spSetMapSquareTexture = Spring.SetMapSquareTexture
local spGetMapSquareTexture = Spring.GetMapSquareTexture
local spGetMyTeamID         = Spring.GetMyTeamID
local spGetGroundHeight     = Spring.GetGroundHeight
local spGetGroundOrigHeight = Spring.GetGroundOrigHeight
local SpGetMetalAmount      = Spring.GetMetalAmount
local SpTestMoveOrder       = Spring.TestMoveOrder
local SpTestBuildOrder      = Spring.TestBuildOrder

local glTexture         = gl.Texture
local glTexRect         = gl.TexRect

local GL_RGBA = 0x1908

local GL_COLOR_ATTACHMENT0_EXT  = 0x8CE0


-----------------------------------------------------------------
-- Includes and classes loading
-----------------------------------------------------------------

local LUASHADER_DIR = "LuaRules/Gadgets/Include/"
local LuaShader = VFS.Include(LUASHADER_DIR .. "LuaShader.lua", nil, VFS.MAP)

-----------------------------------------------------------------
-- Configuration variables
-----------------------------------------------------------------

local DO_MIPMAPS = true

-----------------------------------------------------------------
-- Shader sources
-----------------------------------------------------------------

local vsDiffuse = [[
	#version 150 compatibility

	void main() {
		gl_Position = gl_Vertex;
	}
]]

local fsDiffuse = [[
	#version 150 compatibility
	#line 2088

	uniform vec2 groundMinMax;

	uniform vec4 tileParams; // tx, tz, txMax, tzMax

	uniform vec2 viewPortSize;

	uniform sampler2D terrainHeightTex;
	uniform sampler2D terrainNormalsTex;

	uniform sampler2D lowTex;
	uniform sampler2D midTex;
	uniform sampler2D highTex;


	//  Return value range of -1.0->1.0
	float Perlin2D(vec2 P)
	{
		//  https://github.com/BrianSharpe/Wombat/blob/master/Perlin2D.glsl

		// establish our grid cell and unit position
		vec2 Pi = floor(P);
		vec4 Pf_Pfmin1 = P.xyxy - vec4( Pi, Pi + 1.0 );

		// calculate the hash
		vec4 Pt = vec4( Pi.xy, Pi.xy + 1.0 );
		Pt = Pt - floor(Pt * ( 1.0 / 71.0 )) * 71.0;
		Pt += vec2( 26.0, 161.0 ).xyxy;
		Pt *= Pt;
		Pt = Pt.xzxz * Pt.yyww;
		vec4 hash_x = fract( Pt * ( 1.0 / 951.135664 ) );
		vec4 hash_y = fract( Pt * ( 1.0 / 642.949883 ) );

		// calculate the gradient results
		vec4 grad_x = hash_x - 0.49999;
		vec4 grad_y = hash_y - 0.49999;
		vec4 grad_results = inversesqrt( grad_x * grad_x + grad_y * grad_y ) * ( grad_x * Pf_Pfmin1.xzxz + grad_y * Pf_Pfmin1.yyww );

		// Classic Perlin Interpolation
		grad_results *= 1.4142135623730950488016887242097;  // scale things to a strict -1.0->1.0 range  *= 1.0/sqrt(0.5)
		vec2 blend = Pf_Pfmin1.xy * Pf_Pfmin1.xy * Pf_Pfmin1.xy * (Pf_Pfmin1.xy * (Pf_Pfmin1.xy * 6.0 - 15.0) + 10.0);
		vec4 blend2 = vec4( blend, vec2( 1.0 - blend ) );
		return dot( grad_results, blend2.zxzx * blend2.wwyy );
	}

	vec3 GetTerrainNormal(vec2 uv) {
		vec3 normal;
		normal.xz = texture(terrainNormalsTex, uv).ra;
		normal.y  = sqrt(1.0 - dot(normal.xz, normal.xz));
		return normal;
	}

	#define GetTerrainSlope(uv) (1.0 - GetTerrainNormal(uv).y)

	void main() {
		vec2 tileUV = gl_FragCoord.xy / viewPortSize;
		vec2 mapUV = (tileUV + tileParams.xy) / tileParams.zw;

		float slope = GetTerrainSlope(mapUV);
		float height = texture(terrainHeightTex, mapUV).x;

		const vec3 lowColor = vec3(0.0, 0.0, 1.0);
		const vec3 midColor = vec3(0.0, 1.0, 0.0);
		const vec3 highColor = vec3(0.85, 0.85, 0.85);

		float lowHeightNoise = Perlin2D(mapUV * 16.0);
		float highHeightNoise = Perlin2D(mapUV * 1024.0);

		float lowMul = smoothstep(15.0 + lowHeightNoise * 5.0, lowHeightNoise, height);
		float highMul = smoothstep(150.0 - highHeightNoise * 5.0, 200.0 + highHeightNoise * 20.0, height);

		vec3 heightColor = lowMul * lowColor + highMul * highColor;
		heightColor = mix(midColor, heightColor, lowMul + highMul);

		//gl_FragColor = vec4(mapUV, slope, 1.0);
		//gl_FragColor = vec4(slope, slope, slope, 1.0);
		gl_FragColor = vec4(heightColor, 1.0);
		//gl_FragColor = vec4(1.0);
	}
]]


-----------------------------------------------------------------
-- Local functions and vars
-----------------------------------------------------------------

local updateTiles = {}
local doUpdateTiles

local initGenesis

local diffuseTexes = {}
local diffuseFBOs = {}

local splatDistTex
local splatDistFBO

local diffuseShader

local fullTexQuad

local function Init()
	for x = 0, SQUARES_X - 1 do
		diffuseTexes[x] = {}
		diffuseFBOs[x] = {}

		updateTiles[x] = {}

		for z = 0, SQUARES_Z - 1 do
			diffuseTexes[x][z] = gl.CreateTexture(SQUARE_SIZE, SQUARE_SIZE, {
				format = GL_RGBA,
				border = false,
				min_filter = (DO_MIPMAPS and GL.LINEAR_MIPMAP_LINEAR) or GL.LINEAR,
				mag_filter = GL.LINEAR,
				wrap_s = GL.CLAMP_TO_EDGE,
				wrap_t = GL.CLAMP_TO_EDGE,
			})

			diffuseFBOs[x][z] = gl.CreateFBO({
				color0 = diffuseTexes[x][z],
				drawbuffers = {GL_COLOR_ATTACHMENT0_EXT},
			})

			updateTiles[x][z] = true
			doUpdateTiles = true

			Spring.SetMapSquareTexture(x, z, diffuseTexes[x][z])
		end
	end

	splatDistTex = gl.CreateTexture(SPLAT_X, SPLAT_Z, {
		format = GL_RGBA,
		border = false,
		min_filter = (DO_MIPMAPS and GL.LINEAR_MIPMAP_LINEAR) or GL.LINEAR,
		mag_filter = GL.LINEAR,
		wrap_s = GL.CLAMP_TO_EDGE,
		wrap_t = GL.CLAMP_TO_EDGE,
	})

	splatDistFBO = gl.CreateFBO({
		color0 = splatDistTex,
		drawbuffers = {GL_COLOR_ATTACHMENT0_EXT},
	})

	--Spring.SetMapShadingTexture("$ssmf_splat_distr", splatDistTex)

	initGenesis = true

	diffuseShader = LuaShader({
			vertex = vsDiffuse,
			fragment = fsDiffuse,
			uniformInt = {
				terrainHeightTex = 0,
				terrainNormalsTex = 1,
			},
			uniformFloat = {
				--groundMinMax = {minHeight, maxHeight},
				viewPortSize = {SQUARE_SIZE, SQUARE_SIZE},
			},
		}, "RandomMapGen: Diffuse")
	diffuseShader:Initialize()

	fullTexQuad = gl.CreateList( function ()
		gl.DepthTest(false)
		gl.Blending(false)
		gl.TexRect(-1, -1, 1, 1, true, true) --false, true
	end)
end

local function Clean()
	for x = 0, SQUARES_X - 1 do
		for z = 0, SQUARES_Z - 1 do
			gl.DeleteFBO(diffuseFBOs[x][z])
			gl.DeleteTexture(diffuseTexes[x][z])
		end
	end

	gl.DeleteFBO(splatDistFBO)
	gl.DeleteTexture(splatDistTex)

	diffuseShader:Finalize()

	gl.DeleteList(fullTexQuad)
end

local function UpdateTile(x, z)
	--Spring.Echo("UpdateTile", x, z)
	gl.ActiveFBO(diffuseFBOs[x][z], function()
		--gl.DepthTest(false)
		--gl.Blending(false)
		gl.CallList(fullTexQuad)
	end)

	if DO_MIPMAPS then
		gl.GenerateMipmap(diffuseTexes[x][z])
	end
end

-----------------------------------------------------------------
-- Gadget functions
-----------------------------------------------------------------

function gadget:Initialize()
	Init()
end

function gadget:Shutdown()
	Clean()
end

function gadget:DrawGenesis()
	if initGenesis then

		gl.DepthTest(false)
		gl.Blending(false)
		gl.ActiveFBO(splatDistFBO, gl.Clear, GL.COLOR_BUFFER_BIT, 0.0, 0.0, 0.0, 0.0)

		if DO_MIPMAPS then
			gl.GenerateMipmap(splatDistTex)
		end

		initGenesis = false
	end


	if doUpdateTiles then
		diffuseShader:ActivateWith( function()

			glTexture(0, "$heightmap")
			glTexture(1, "$normals")

			--local minHeight, maxHeight = Spring.GetGameRulesParam("ground_min_override"), Spring.GetGameRulesParam("ground_max_override")
			local minHeight, maxHeight = Spring.GetGroundExtremes()

			diffuseShader:SetUniform("groundMinMax", minHeight, maxHeight)

			for x = 0, SQUARES_X - 1 do
				for z = 0, SQUARES_Z - 1 do
					if updateTiles[x][z] then
						diffuseShader:SetUniform("tileParams", x, z, SQUARES_X, SQUARES_Z)
						UpdateTile(x, z)
					end
				end
			end

			glTexture(0, false)
			glTexture(1, false)

		end)

		doUpdateTiles = false
	end

end


function gadget:UnsyncedHeightMapUpdate(x1, z1, x2, z2)
	local tx1, tz1 = math.floor((x1 * BLOCK_SIZE    ) / SQUARE_SIZE), math.floor((z1 * BLOCK_SIZE    ) / SQUARE_SIZE)
	local tx2, tz2 = math.floor((x2 * BLOCK_SIZE - 1) / SQUARE_SIZE), math.floor((z2 * BLOCK_SIZE - 1) / SQUARE_SIZE)

	for tx = tx1, tx2 do
		for tz = tz1, tz2 do
			--Spring.Echo("updateTiles", tx, tz)
			doUpdateTiles = true
			updateTiles[tx][tz] = true
		end
	end
end

--// Workaround: unsynced LuaRules doesn't receive Shutdown events
rmgtex2Shutdown = Script.CreateScream()
rmgtex2Shutdown.func = function() gadget:Shutdown() end


