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
local band, shl, sar, tobit, tobinary = bit.band, bit.lshift, bit.arshift, bit.tobit, bit.tobinary

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
  local nnn = nn
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end

  for i = 1,nn-1 do
    if (tobit(actlist[i]) == -1) then
	    nnn = nnn - 2
    else if (tobit(actlist[i]) == -2) then
	    nnn = nnn - 3
    else if (tobit(actlist[i]) == -3) then
	    nnn = nnn - 3
    else if (tobit(actlist[i]) == -4) then
	    nnn = nnn - 3
    end
    end
    end
    end
  end
  out:write("static const unsigned long ", name, "[", nnn, "] = {\n")

  local i = 1
  while i <= nn - 1 do
    if (tobit(actlist[i]) == -1) then
      assert(out:write("0b00"))
      nnn = i + 2 -- X1
      assert(out:write(tobinary(actlist[nnn], 31)))
      nnn = i + 1 -- X0
      assert(out:write(tobinary(actlist[nnn], 31), "L,\n"))
      i = i + 3
    else
      assert(out:write(tobinary(actlist[i], 31), "L,\n"))
      i = i + 1
    end
  end
  assert(out:write("0b", tobinary(actlist[nn], 32), "L\n};\n\n"))
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
-- "D": Dest Reg in X slot.
-- "A": SrcA Reg in X slot.
-- "B": SrcB Reg in X slot.
-- "I": Imm16 in X slot.
-- "i": Imm8 in X slot.

local map_op = {
  -- Bundle Markers.
  B_X_0 =	"FFFFFFFF",
  B_Y0_0 =	"FFFFFFFE",
  B_Y1_0 =	"FFFFFFFD",
  B_Y2_0 =	"FFFFFFFC",

  -- Arithmetic Instructions.
  B_move_x0_2 =		"5107F000DA",
  B_move_x1_2 =		"5077F000DA",
  B_add_x0_3 =		"500C0000DAB",
  B_add_x1_3 =		"500C0000DAB",
  B_addi_x0_3 =		"40100000DAi",
  B_addi_x1_3 =		"30100000DAi",
  B_addli_x0_3 =	"10000000DAI",
  B_addli_x1_3 =	"00000000DAI",
  B_moveli_x0_2 =	"10000FC0DI",
  B_moveli_x1_2 =	"00000FC0DI",
  B_movei_x0_2 =	"40100FC0DI",
  B_movei_x1_2 =	"30100FC0DI",
  B_addlo_x0_2 =	"10000000DO",
  B_addlo_x1_2 =	"00000000DO",
  B_shl16insli_x0_3 =	"70000000DAI",
  B_shl16insli_x1_3 =	"70000000DAI",
  B_sub_x0_3 =		"51440000DAB",
  B_sub_x1_3 =		"50D00000DAB",

  -- Logical Instructions.
  B_and_x0_3 =		"50100000DAB",
  B_and_x1_3 =		"50100000DAB",
  B_or_x0_3 =		"51040000DAB",
  B_or_x1_3 =		"50740000DAB",
  B_nor_x0_3 =		"51000000DAB",
  B_nor_x1_3 =		"50700000DAB",
  B_xor_x0_3 =		"52800000DAB",
  B_xor_x1_3 =		"51AC0000DAB",
  B_xori_x0_3 =		"41400000DAi",
  B_xori_x1_3 =		"32D00000DAi",
  B_andi_x0_3 =		"40300000DAi",
  B_andi_x1_3 =		"30300000DAi",
  B_ori_x0_3 =		"40700000DAi",
  B_ori_x1_3 =		"31800000DAi",
  B_shl_x0_3 =		"51280000DAB",
  B_shl_x1_3 =		"50980000DAB",
  B_shli_x0_3 =		"60080000DAi",
  B_shli_x1_3 =		"60080000DAi",
  B_shru_x0_3 =		"51340000DAB",
  B_shru_x1_3 =		"50A40000DAB",
  B_shrui_x0_3 =	"60140000DAi",
  B_shrui_x1_3 =	"60140000DAi",
  B_shrs_x0_3 =		"512C0000DAB",
  B_shrs_x1_3 =		"509C0000DAB",
  B_shrsi_x0_3 =	"60100000DAi",
  B_shrsi_x1_3 =	"60100000DAi",
  B_bfextu_x0_4 =	"35000000DAGH",
  B_bfexts_x0_4 =	"34000000DAGH",
  B_bfins_x0_4 =	"36000000DAGH",
  B_cmoveqz_x0_3 =	"50140000DAB",
  B_cmovnez_x0_3 =	"50180000DAB",

  -- Memory Instructions.
  B_st_x1_2 =		"50C40000AB",
  B_st4_x1_2 =		"50B00000AB",
  B_st2_x1_2 =		"50AC0000AB",
  B_st1_x1_2 =		"50A80000AB",
  B_ld_x1_2 =		"50D5D000DA",
  B_ld4u_x1_2 =		"50D54000DA",
  B_ld4s_x1_2 =		"50D53000DA",
  B_ld2u_x1_2 =		"50D52000DA",
  B_ld2s_x1_2 =		"50D51000DA",
  B_ld1u_x1_2 =		"50D50000DA",
  B_ld1s_x1_2 =		"50D4F000DA",

  -- Control Instructions.
  B_j_x1_1 =		"48000000J",
  B_jr_x1_1 =		"50D4E000A",
  B_jal_x1_1 =		"40000000J",
  B_jalr_x1_1 =		"50D4C000A",
  B_b_x1_1 =		"28800FC0K",
  B_beqz_x1_2 =		"28800000AK",
  B_bnez_x1_2 =		"2F800000AK",
  B_bltz_x1_2 =		"2E800000AK",
  B_blez_x1_2 =		"2D800000AK",
  B_bgtz_x1_2 =		"2A800000AK",
  B_bgez_x1_2 =		"29800000AK",
  B_lnk_x1_1 =		"50D5E000D",

  -- Compare Instructions.
  B_cmpeq_x0_3 =	"501C0000DAB",
  B_cmpeq_x1_3 =	"50140000DAB",
  B_cmpne_x0_3 =	"50300000DAB",
  B_cmpne_x1_3 =	"50300000DAB",
  B_cmplts_x0_3 =	"50280000DAB",
  B_cmplts_x1_3 =	"50280000DAB",
  B_cmpltu_x0_3 =	"502C0000DAB",
  B_cmpltu_x1_3 =	"502C0000DAB",
  B_cmpleu_x0_3 =	"50240000DAB",
  B_cmpleu_x1_3 =	"50240000DAB",
  B_cmpeqi_x0_3 =	"40400000DAi",
  B_cmpeqi_x1_3 =	"30400000DAi",
  B_cmpltsi_x0_3 =	"40500000DAi",
  B_cmpltsi_x1_3 =	"30500000DAi",
  B_cmpltui_x0_3 =	"40600000DAi",
  B_cmpltui_x1_3 =	"30600000DAi",

  -- Float
  B_mul_hu_lu_x0_3 =	"50EC0000DAB",
  B_mul_lu_lu_x0_3 =	"50F80000DAB",
  B_mul_hu_hu_x0_3 =	"50E40000DAB",
  B_mula_hu_lu_x0_3 =	"50C00000DAB",
  B_fdouble_pack1_x0_3 =	"50740000DAB",
  B_fdouble_pack2_x0_3 =	"50780000DAB",
  B_fdouble_add_flags_x0_3 =	"506C0000DAB",
  B_fdouble_sub_flags_x0_3 =	"507C0000DAB",
  B_fdouble_mul_flags_x0_3 =	"50700000DAB",
  B_fdouble_addsub_x0_3 =	"50680000DAB",
  B_fdouble_unpack_min_x0_3 =	"50840000DAB",
  B_fdouble_unpack_max_x0_3 =	"50800000DAB",

  -- Float
  B_fnop_x0_0 =		"51483000",
  B_fnop_x1_0 =		"50D46000",
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
      return shl(r, 6)
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

-- bundle version
map_op[".template__"] = function(params, template, nparams)
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1

  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 2 positions (ins/ext).
  if secpos+2 > maxsecpos then wflush() end
  local pos = wpos()

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do

    -- X mode
    if p == "A" then
      op = op + shl(parse_gpr(params[n]), 6); n = n + 1
    elseif p == "B" then
      op = op + shl(parse_gpr(params[n]), 12); n = n + 1
    elseif p == "D" then
      op = op + parse_gpr(params[n]); n = n + 1
    elseif p == "O" then
      op = op + parse_rbo_x1_imm16(params[n]); n = n + 1
    elseif p == "G" then
      op = op + shl(parse_imm(params[n], 6, 0, 0, false), 18); n = n + 1
    elseif p == "H" then
      op = op + shl(parse_imm(params[n], 6, 0, 0, false), 12); n = n + 1
    elseif p == "I" then
      op = op + shl(parse_imm(params[n], 16, 0, 0, true), 12); n = n + 1
    elseif p == "i" then
      op = op + shl(parse_imm(params[n], 8, 0, 0, true), 12); n = n + 1
    elseif p == "K" then
      local mode, n, s = parse_label(params[n], false)
      waction("REL_"..mode.."_X1_BR", n, s, 1)
    elseif p == "J" then
      local mode, n, s = parse_label(params[n], false)
      waction("REL_"..mode.."_X1_J", n, s, 1)
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

