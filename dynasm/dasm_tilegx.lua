------------------------------------------------------------------------------
-- DynASM TileGX module.
--
-- Copyright (C) 2005-2013 Mike Pall. All rights reserved.
-- Copyright (C) 2013-2013 Tilera Corporation. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

-- Module information:
local _info = {
  arch =	"tilegx",
  description =	"DynASM TileGX module",
  version =	"1.3.0",
  vernum =	 10300,
  release =	"2013-11-08",
  author =	"Jiong Wang",
  license =	"MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable = assert, setmetatable
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch = _s.match, _s.gmatch
local concat, sort = table.concat, table.sort
local bit = bit or require("bit")
local band, shl, shll, sar = bit.band, bit.lshift, bit.llshift, bit.arshift

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG_X1_BR", "REL_LG_X1_J", "LABEL_LG",
  "REL_PC_X1_BR", "REL_PC_X1_J", "LABEL_PC", "IMM",
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n-1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end
  out:write("static const unsigned long ", name, "[", nn, "] = {\n")
  for i = 1,nn-1 do
    if (sub(string.format("%016X", actlist[i]), 1, 8) == "00000000") then
      -- X0 bundle.
      assert(out:write("0x286A3000", string.format("%08X", actlist[i]), "L,\n"))
    else
      assert(out:write("0x", string.format("%016X", actlist[i]), "L,\n"))
    end
  end
  if (sub(string.format("%016X", actlist[nn]), 1, 8) == "00000000") then
    -- X0 bundle.
    assert(out:write("0x286A3000", string.format("%08X", actlist[nn]), "L,\n"))
  else
    assert(out:write("0x", string.format("%016X", actlist[nn]), "L\n};\n\n"))
  end
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  assert(n >= 0 and n <= 0xffffffffffffffff and n % 1 == 0, "word out of range")
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(0xff00000000000000 + w * 0x1000000000000 + (val or 0) * 0x1000)
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

-- Put escaped word.
local function wputw(n)
  if n >= 0xff000000 then waction("ESC") end
  wputxw(n)
end

-- Reserve position for word.
local function wpos()
  local pos = #actlist+1
  actlist[pos] = ""
  return pos
end

-- Store word to reserved position.
local function wputpos(pos, n)
  assert(n >= 0 and n <= 0xffffffffffffffff and n % 1 == 0, string.format("%016X", n).."word out of range")
  actlist[pos] = n
end

------------------------------------------------------------------------------

-- Global label name -> global label number. With auto assignment on 1st use.
local next_global = 20
local map_global = setmetatable({}, { __index = function(t, name)
  if not match(name, "^[%a_][%w_]*$") then werror("bad global label") end
  local n = next_global
  if n > 2047 then werror("too many global labels") end
  next_global = n + 1
  t[name] = n
  return n
end})

-- Dump global labels.
local function dumpglobals(out, lvl)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("Global labels:\n")
  for i=20,next_global-1 do
    out:write(format("  %s\n", t[i]))
  end
  out:write("\n")
end

-- Write global label enum.
local function writeglobals(out, prefix)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("enum {\n")
  for i=20,next_global-1 do
    out:write("  ", prefix, t[i], ",\n")
  end
  out:write("  ", prefix, "_MAX\n};\n")
end

-- Write global label names.
local function writeglobalnames(out, name)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("static const char *const ", name, "[] = {\n")
  for i=20,next_global-1 do
    out:write("  \"", t[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Extern label name -> extern label number. With auto assignment on 1st use.
local next_extern = 0
local map_extern_ = {}
local map_extern = setmetatable({}, { __index = function(t, name)
  -- No restrictions on the name for now.
  local n = next_extern
  if n > 2047 then werror("too many extern labels") end
  next_extern = n + 1
  t[name] = n
  map_extern_[n] = name
  return n
end})

-- Dump extern labels.
local function dumpexterns(out, lvl)
  out:write("Extern labels:\n")
  for i=0,next_extern-1 do
    out:write(format("  %s\n", map_extern_[i]))
  end
  out:write("\n")
end

-- Write extern label names.
local function writeexternnames(out, name)
  out:write("static const char *const ", name, "[] = {\n")
  for i=0,next_extern-1 do
    out:write("  \"", map_extern_[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Arch-specific maps.
local map_archdef = { sp="r54", lr="r55", zero="r63" } -- Ext. register name -> int. name.

local map_type = {}		-- Type name -> { ctype, reg }
local ctypenum = 0		-- Type number (for Dt... macros).

-- Reverse defines for registers.
function _M.revdef(s)
  if s == "r54" then return "sp"
  elseif s == "r55" then return "lr"
  elseif s == "r63" then return "zero" end
  return s
end

------------------------------------------------------------------------------

-- Template strings for TileGX instructions.
-- "D": Dest Reg in X1 slot.
-- "A": SrcA Reg in X1 slot.
-- "B": SrcB Reg in X1 slot.
-- "I": Imm16 in X1 slot.
-- "i": Imm8 in X1 slot.

local map_op = {
  -- Arithmetic Instructions.
  move_2 =		"283BF80051483000DA",
  add_3 =		"2806000051483000DAB",
  addi_3 =		"1808000051483000DAi",
  moveli_2 =		"000007E051483000DI",
  addli_3 =		"0000000051483000DAI",
  addlo_2 =		"0000000051483000DO",
  shl16insli_3 =	"3800000051483000DAI",
  sub_3 =		"2868000051483000DAB",

  -- Logical Instructions.
  and_3 =		"2808000051483000DAB",  
  or_3 =		"283A000051483000DAB",  
  nor_3 =		"2838000051483000DAB",  
  xor_3 =		"28D6000051483000DAB",  
  xori_3 =		"1968000051483000DAi",  
  andi_3 =		"1818000051483000DAi",
  ori_3 =		"18C0000051483000DAi",
  shl_3 =		"284C000051483000DAB",
  shli_3 =		"3004000051483000DAi",
  shru_3 =		"2852000051483000DAB",
  shrui_3 =		"300A000051483000DAi",
  shrs_3 =		"284E000051483000DAB",
  shrsi_3 =		"3008000051483000DAi",
  -- bfextu_4 =		"286A300035000000EFGH",
  bfextu_4 =		"0000000035000000EFGH",
  bfexts_4 =		"0000000034000000EFGH",
  bfins_4 =		"0000000036000000EFGH",
  cmoveqz_3 =		"0000000050140000EFC",
  cmovnez_3 =		"0000000050180000EFC",

  -- Memory Instructions.
  st_2 =		"DE064000340C3000ab",
  st4_2 =		"DE064000300C3000ab",
  st2_2 =		"DC064000340C3000ab",
  st1_2 =		"DC064000300C3000ab",
  ld_2 =		"9E064000340C3000ba",
  ld4u_2 =		"9E064000300C3000ba",
  ld2u_2 =		"5E064000340C3000ba",
  ld1u_2 =		"5C064000340C3000ba",
  ld4s_2 =		"9C064000340C3000ba",
  ld2s_2 =		"5E064000300C3000ba",
  ld1s_2 =		"5C064000300C3000ba",

  -- Control Instructions.
  jr_1 =		"286A700051483000A",
  jal_1 =		"2000000051483000J",
  j_1 =			"2400000051483000J",
  jalr_1 =		"286A600051483000A",
  beqz_2 =		"1440000051483000AK",
  bnez_2 =		"17C0000051483000AK",
  bltz_2 =		"1740000051483000AK",
  blez_2 =		"16C0000051483000AK",
  bgtz_2 =		"1540000051483000AK",
  bgez_2 =		"14C0000051483000AK",
  b_1 = 		"144007e051483000K",

  -- Compare Instructions.
  cmpeq_3 =		"280a000051483000DAB",
  cmpne_3 =		"2818000051483000DAB",
  cmplts_3 =		"2814000051483000DAB",
  cmpltu_3 =		"2816000051483000DAB",
  cmpltsi_3 =		"1828000051483000DAi",
  cmpltui_3 =		"1830000051483000DAi",

  -- Float
  mul_hu_lu_3 =		"0000000050EC0000EFC",
  mul_lu_lu_3 =		"0000000050F80000EFC",
  mula_hu_lu_3 =	"0000000050C00000EFC",
  mul_hu_hu_3 =		"0000000050E40000EFC",
  fdouble_pack1_3 =	"0000000050740000EFC",
  fdouble_pack2_3 =	"0000000050780000EFC",
  fdouble_add_flags_3 =	"00000000506C0000EFC",
  fdouble_sub_flags_3 =	"00000000507C0000EFC",
  fdouble_mul_flags_3 =	"0000000050700000EFC",
  fdouble_addsub_3 =	"0000000050680000EFC",
  fdouble_unpack_min_3 =	"0000000050840000EFC",
  fdouble_unpack_max_3 =	"0000000050800000EFC",
}

------------------------------------------------------------------------------

local function parse_gpr(expr)
  local tname, ovreg = match(expr, "^([%w_]+):(r[1-6]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^r([1-6]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 63 then return r, tp end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_imm(imm, bits, shift, scale, signed)
  local n = tonumber(imm)
  if n then
    local m = sar(n, scale)
    if shl(m, scale) == n then
      if signed then
	local s = sar(m, bits-1)
	if s == 0 then return shl(m, shift)
	elseif s == -1 then return shl(m + shl(1, bits), shift) end
      else
	if sar(m, bits) == 0 then return shl(m, shift) end
      end
    end
    werror("out of range immediate `"..imm.."'")
  elseif match(imm, "^[rf]([1-3]?[0-9])$") or
	 match(imm, "^([%w_]+):([rf][1-3]?[0-9])$") then
    werror("expected immediate operand, got register")
  else
    waction("IMM", (signed and 2147483648 or 0)+scale*67108864+bits*2097152+shift*65536, imm)
    return 0
  end
end

local function parse_rbo_x1_imm16(disp)
  local reg, tailr = match(disp, "^([%w_:]+)%s*(.*)$")
  if reg and tailr ~= "" then
    local r, tp = parse_gpr(reg)
    if tp then
      waction("IMM", 2147483648 + 16 * 2097152, format(tp.ctypefmt, tailr))
      return shll(r, 37)
    end
  end
  werror("bad displacement `"..disp.."'")
end

local function parse_label(label, def)
  local prefix = sub(label, 1, 2)
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)]
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label)
    end
  else
    -- [<>][1-9] (local label reference)
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10)
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname]
    end
  end
  werror("bad label `"..label.."'")
end

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
map_op[".template__"] = function(params, template, nparams)
  if not params then return sub(template, 17) end
  local op = tonumber(sub(template, 1, 16), 16)
  local n = 1

  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 2 positions (ins/ext).
  if secpos+2 > maxsecpos then wflush() end
  local pos = wpos()

  -- Process each character.
  for p in gmatch(sub(template, 17), ".") do

    -- X mode
    if p == "A" then
      op = op + shll(parse_gpr(params[n]), 37); n = n + 1
    elseif p == "B" then
      op = op + shll(parse_gpr(params[n]), 43); n = n + 1
    elseif p == "C" then
      op = op + shll(parse_gpr(params[n]), 12); n = n + 1
    elseif p == "D" then
      op = op + shll(parse_gpr(params[n]), 31); n = n + 1
    elseif p == "O" then
      op = op + parse_rbo_x1_imm16(params[n]); n = n + 1
    elseif p == "E" then
      op = op + parse_gpr(params[n]); n = n + 1
    elseif p == "F" then
      op = op + shll(parse_gpr(params[n]), 6); n = n + 1
    elseif p == "G" then
      op = op + shll(parse_imm(params[n], 6, 0, 0, false), 18); n = n + 1
    elseif p == "H" then
      op = op + shll(parse_imm(params[n], 6, 0, 0, false), 12); n = n + 1
    elseif p == "I" then
      op = op + shll(parse_imm(params[n], 16, 0, 0, true), 43); n = n + 1
    elseif p == "i" then
      op = op + shll(parse_imm(params[n], 8, 0, 0, true), 43); n = n + 1
    elseif p == "K" then
      local mode, n, s = parse_label(params[n], false)
      waction("REL_"..mode.."_X1_BR", n, s, 1)
    elseif p == "J" then
      local mode, n, s = parse_label(params[n], false)
      waction("REL_"..mode.."_X1_J", n, s, 1)

    -- Y mode
    elseif p == "a" then
      op = op + shll(parse_gpr(params[n]), 20); n = n + 1
    elseif p == "b" then
      op = op + shll(parse_gpr(params[n]), 51); n = n + 1
    else
      assert(false)
    end
  end
  wputpos(pos, op)
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

-- Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params)
  if not params then return "prefix" end
  local prefix = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobals(out, prefix) end)
end

-- Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobalnames(out, name) end)
end

-- Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeexternnames(out, name) end)
end

------------------------------------------------------------------------------

-- Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params)
  if not params then return "[1-9] | ->global | =>pcexpr" end
  if secpos+1 > maxsecpos then wflush() end
  local mode, n, s = parse_label(params[1], true)
  if mode == "EXT" then werror("bad label definition") end
  waction("LABEL_"..mode, n, s, 1)
end

------------------------------------------------------------------------------

-- Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    local n = tonumber(p)
    if not n then werror("bad immediate `"..p.."'") end
    if n < 0 then n = n + 2^32 end
    wputw(n)
    if secpos+2 > maxsecpos then wflush() end
  end
end

-- Alignment pseudo-opcode.
map_op[".align_1"] = function(params)
  if not params then return "numpow2" end
  if secpos+1 > maxsecpos then wflush() end
  local align = tonumber(params[1])
  if align then
    local x = align
    -- Must be a power of 2 in the range (2 ... 256).
    for i=1,8 do
      x = x / 2
      if x == 1 then
	waction("ALIGN", align-1, nil, 1) -- Action byte is 2**n-1.
	return
      end
    end
  end
  werror("bad alignment")
end

------------------------------------------------------------------------------

-- Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3"] = function(params, nparams)
  if not params then
    return nparams == 2 and "name, ctype" or "name, ctype, reg"
  end
  local name, ctype, reg = params[1], params[2], params[3]
  if not match(name, "^[%a_][%w_]*$") then
    werror("bad type name `"..name.."'")
  end
  local tp = map_type[name]
  if tp then
    werror("duplicate type `"..name.."'")
  end
  -- Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")"
  -- Add new type and emit shortcut define.
  local num = ctypenum + 1
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  }
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype))
  ctypenum = num
end
map_op[".type_2"] = map_op[".type_3"]

-- Dump type definitions.
local function dumptypes(out, lvl)
  local t = {}
  for name in pairs(map_type) do t[#t+1] = name end
  sort(t)
  out:write("Type definitions:\n")
  for _,name in ipairs(t) do
    local tp = map_type[name]
    local reg = tp.reg or ""
    out:write(format("  %-20s %-20s %s\n", name, tp.ctype, reg))
  end
  out:write("\n")
end

------------------------------------------------------------------------------

-- Set the current section.
function _M.section(num)
  waction("SECTION", num)
  wflush(true) -- SECTION is a terminal action.
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = map_coreop })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------

