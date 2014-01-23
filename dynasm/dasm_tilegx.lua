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
local band, shl, shr, sar, tobit, tobinary = bit.band, bit.lshift, bit.rshift, bit.arshift, bit.tobit, bit.tobinary

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG_X1_BR", "REL_LG_X1_J", "LABEL_LG",
  "REL_PC_X1_BR", "REL_PC_X1_J", "LABEL_PC", "IMM_X0", "IMM_X1"
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
    elseif (tobit(actlist[i]) == -2) then
	    nnn = nnn - 3
    elseif (tobit(actlist[i]) == -3) then
	    nnn = nnn - 3
    elseif (tobit(actlist[i]) == -4) then
	    nnn = nnn - 3
    end
  end
  out:write("static const unsigned long ", name, "[", nnn, "] = {\n")

  local i = 1
  while i <= nn - 1 do
    if tobit(actlist[i]) == -1 then
      assert(out:write("0b00"))
      if (tobit(actlist[i + 2]) >= 0) then
	local x1 = tobinary(actlist[i + 2], 31)
	local x0 = tobinary(actlist[i + 1], 31)
        assert(out:write(x1, x0, "L,\n"))
        i = i + 3
      else -- X0 has an accompany relocation which occupies X1 slot.
	local x1 = tobinary(actlist[i + 3], 31)
	local x0 = tobinary(actlist[i + 1], 31)
	local x0_r = tobinary(actlist[i + 2], 32)
        assert(out:write(x1, x0, "L,\n"))
        assert(out:write("0b11111111111111111111111111111111", x0_r, "L,\n"))
        i = i + 4
      end
    elseif tobit(actlist[i]) == -2 or tobit(actlist[i]) == -3 or tobit(actlist[i]) == -4 then
      if tobit(actlist[i]) == -2 then
        assert(out:write("0b01"))
      elseif tobit(actlist[i]) == -3 then
        assert(out:write("0b10"))
      elseif tobit(actlist[i]) == -4 then
        assert(out:write("0b11"))
      end

      if (tobit(actlist[i + 2]) >= 0) then
	local y2 = tobinary(actlist[i+3], 14)
	local y1 = tobinary(actlist[i+2], 24)
	local y0 = tobinary(actlist[i+1], 24)
        assert(out:write(sub(y1, 1, 4), sub(y2, 1, 7), sub(y1, 5, 24),
	       sub(y0, 1, 4), sub(y2, 8, 14), sub(y0, 5, 24), "L,\n"))
        i = i + 4
      else -- Y0 has an accompany relocation which occupies Y1 slot.
        assert(0, "relocation in Y bundle TBD")
      end

    else
      assert(out:write("0b11111111111111111111111111111111", tobinary(actlist[i], 32), "L,\n"))
      i = i + 1
    end
  end
  assert(out:write("0b11111111111111111111111111111111", tobinary(actlist[nn], 32), "L\n};\n\n"))
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(0xff000000 + w * 0x10000 + (val or 0))
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  local nn = #actlist
  local nnn = nn

  if nn > 2 then
  for i = 1,nn do
    if (tobit(actlist[i]) == -1) then
	    nnn = nnn - 2
    elseif (tobit(actlist[i]) == -2) then
	    nnn = nnn - 3
    elseif (tobit(actlist[i]) == -3) then
	    nnn = nnn - 3
    elseif (tobit(actlist[i]) == -4) then
	    nnn = nnn - 3
    end
  end
  end

  if nnn == actargs[1] then return end -- Nothing to flush.
  if not term then
    waction("STOP")
    nnn = nnn + 1
  end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)

  actargs = { nnn } -- Actionlist offset is 1st arg to next dasm_put().
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
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
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

-- template[9]
-- "0": Start of X bundle.
-- "1": In X bundle.
-- "2": End of X bundle.
-- "3": Start of Y bundle.
-- "4": In Y bundle.
-- "5": End of Y bundle.

local map_op = {
  -- Bundle Markers.
  B_X_0 =	"FFFFFFFF0",
  B_Y1_0 =	"FFFFFFFE3",
  B_Y2_0 =	"FFFFFFFD3",
  B_Y3_0 =	"FFFFFFFC3",

  -- Arithmetic Instructions.
  B_move_x0_2 =		"5107F0001DA",
  B_move_x1_2 =		"5077F0002DA",
  B_move_y0_2 =		"00ABF0004DA",
  B_move_y1_2 =		"00BBF0004DA",
  B_add_x0_3 =		"500C00001DAB",
  B_add_x1_3 =		"500C00002DAB",
  B_add_y0_3 =		"005400004DAB",
  B_add_y1_3 =		"006400004DAB",
  B_addx_x0_3 =		"500800001DAB",
  B_addx_x1_3 =		"500800002DAB",
  B_addi_x0_3 =		"401000001DAe",
  B_addi_x1_3 =		"301000002DAE",
  B_addxi_x0_3 =	"402000001DAe",
  B_addxi_x1_3 =	"302000002DAE",
  -- Y0/Y1 IMM8 relocation offset are the same with X0/X1,
  -- so we reuse e/E flag for Y bundle.
  B_addi_y0_3 =		"000000004DAe",
  B_addi_y1_3 =		"001000004DAE",
  B_addli_x0_3 =	"100000001DAi",
  B_addli_x1_3 =	"000000002DAI",
  B_moveli_x0_2 =	"10000FC01Di",
  B_moveli_x1_2 =	"00000FC02DI",
  B_movei_x0_2 =	"40100FC01De",
  B_movei_x1_2 =	"30100FC02DE",
  B_movei_y0_2 =	"00000FC04De",
  B_movei_y1_2 =	"00100FC04DE",
  B_addlo_x0_2 =	"100000001Do",
  B_addlo_x1_2 =	"000000002DO",
  B_shl16insli_x0_3 =	"700000001DAi",
  B_shl16insli_x1_3 =	"700000002DAI",
  B_sub_x0_3 =		"514400001DAB",
  B_sub_x1_3 =		"50D000002DAB",
  B_subx_x0_3 =		"514000001DAB",
  B_subx_x1_3 =		"50CC00002DAB",
  B_v4int_l_x0_3 =	"526000001DAB",
  B_v4int_l_x1_3 =	"518C00002DAB",
  B_mulx_x0_3 =		"50D000001DAB",

  -- Logical Instructions.
  B_and_x0_3 =		"501000001DAB",
  B_and_x1_3 =		"501000002DAB",
  B_or_x0_3 =		"510400001DAB",
  B_or_x1_3 =		"507400002DAB",
  B_nor_x0_3 =		"510000001DAB",
  B_nor_x1_3 =		"507000002DAB",
  B_xor_x0_3 =		"528000001DAB",
  B_xor_x1_3 =		"51AC00002DAB",
  B_xori_x0_3 =		"414000001DAe",
  B_xori_x1_3 =		"32D000002DAE",
  B_andi_x0_3 =		"403000001DAe",
  B_andi_x1_3 =		"303000002DAE",
  B_andi_y0_3 =		"002000004DAe",
  B_andi_y1_3 =		"003000004DAE",
  B_ori_x0_3 =		"407000001DAe",
  B_ori_x1_3 =		"318000002DAE",
  B_shl_x0_3 =		"512800001DAB",
  B_shl_x1_3 =		"509800002DAB",
  B_shlx_x0_3 =		"512400001DAB",
  B_shlx_x1_3 =		"509400002DAB",
  B_shli_x0_3 =		"600800001DAe",
  B_shli_x1_3 =		"600800002DAE",
  B_shli_y0_3 =		"00F400004DAe",
  B_shli_y1_3 =		"00E400004DAE",
  B_shru_x0_3 =		"513400001DAB",
  B_shru_x1_3 =		"50A400002DAB",
  B_shrui_x0_3 =	"601400001DAe",
  B_shrui_x1_3 =	"601400002DAE",
  B_shrui_y0_3 =	"00FC00004DAe",
  B_shrui_y1_3 =	"00EC00004DAE",
  B_shruxi_x0_3 =	"601800001DAe",
  B_shruxi_x1_3 =	"601800002DAE",
  B_shrs_x0_3 =		"512C00001DAB",
  B_shrs_x1_3 =		"509C00002DAB",
  B_shrsi_x0_3 =	"601000001DAe",
  B_shrsi_x1_3 =	"601000002DAE",
  B_bfextu_x0_4 =	"350000001DAGH",
  B_bfexts_x0_4 =	"340000001DAGH",
  B_bfins_x0_4 =	"360000001DAGH",
  B_cmoveqz_x0_3 =	"501400001DAB",
  B_cmovnez_x0_3 =	"501800001DAB",
  B_revbytes_x0_2 =	"514880001DA",
  B_rotl_x0_3 =		"510800001DAB",
  B_rotl_x1_3 =		"507800001DAB",

  -- Memory Instructions.
  B_st_x1_2 =		"50C400002AB",
  B_st_y2_2 =		"000020405DL",
  B_st4_x1_2 =		"50B000002AB",
  B_st4_y2_2 =		"000020005DL",
  B_st2_x1_2 =		"50AC00002AB",
  B_st1_x1_2 =		"50A800002AB",
  B_st_add_x1_3 =	"320000002ABz",
  B_ld_x1_2 =		"50D5D0002DA",
  B_ld_y2_2 =		"000020405LD",
  B_ld4u_x1_2 =		"50D540002DA",
  B_ld4u_y2_2 =		"000020005LD",
  B_ld4s_x1_2 =		"50D530002DA",
  B_ld4s_y2_2 =		"000000405LD",
  B_ld2u_x1_2 =		"50D520002DA",
  B_ld2u_y2_2 =		"000020405LD",
  B_ld2s_x1_2 =		"50D510002DA",
  B_ld1u_x1_2 =		"50D500002DA",
  B_ld1u_y2_2 =		"000000405LD",
  B_ld1s_x1_2 =		"50D4F0002DA",
  B_ld_add_x1_3 =	"314000002DAE",
  B_ld4u_add_x1_3 =	"30C000002DAE",
  B_ld4s_add_x1_3 =	"30B000002DAE",

  -- Control Instructions.
  B_j_x1_1 =		"480000002J",
  B_jr_x1_1 =		"50D4E0002A",
  B_jrp_x1_1 =		"50D4D0002A",
  B_jal_x1_1 =		"400000002J",
  B_jalr_x1_1 =		"50D4C0002A",
  B_b_x1_1 =		"28800FC02K",
  B_beqz_x1_2 =		"288000002AK",
  B_beqzt_x1_2 =	"280000002AK",
  B_bnez_x1_2 =		"2F8000002AK",
  B_bnezt_x1_2 =	"2F0000002AK",
  B_bltz_x1_2 =		"2E8000002AK",
  B_blez_x1_2 =		"2D8000002AK",
  B_bgtz_x1_2 =		"2A8000002AK",
  B_bgez_x1_2 =		"298000002AK",
  B_lnk_x1_1 =		"50D5E0002D",

  -- Compare Instructions.
  B_cmpeq_x0_3 =	"501C00001DAB",
  B_cmpeq_x1_3 =	"501400002DAB",
  B_cmpne_x0_3 =	"503000001DAB",
  B_cmpne_x1_3 =	"503000002DAB",
  B_cmpne_y1_3 =	"009C00004DAB",
  B_cmplts_x0_3 =	"502800001DAB",
  B_cmplts_x1_3 =	"502800002DAB",
  B_cmpltu_x0_3 =	"502C00001DAB",
  B_cmpltu_x1_3 =	"502C00002DAB",
  B_cmpltu_y0_3 =	"007C00004DAB",
  B_cmpltu_y1_3 =	"008C00004DAB",
  B_cmples_x0_3 =	"502000001DAB",
  B_cmples_x1_3 =	"502000002DAB",
  B_cmpleu_x0_3 =	"502400001DAB",
  B_cmpleu_x1_3 =	"502400002DAB",
  B_cmpeqi_x0_3 =	"404000001DAe",
  B_cmpeqi_x1_3 =	"304000002DAE",
  B_cmpeqi_y0_3 =	"003000004DAi",
  B_cmpltsi_x0_3 =	"405000001DAe",
  B_cmpltsi_x1_3 =	"305000002DAE",
  B_cmpltui_x0_3 =	"406000001DAe",
  B_cmpltui_x1_3 =	"306000002DAE",

  -- Float
  B_mul_hu_lu_x0_3 =	"50EC00001DAB",
  B_mul_lu_lu_x0_3 =	"50F800001DAB",
  B_mul_hu_hu_x0_3 =	"50E400001DAB",
  B_mula_hu_lu_x0_3 =	"50C000001DAB",
  B_fdouble_pack1_x0_3 =	"507400001DAB",
  B_fdouble_pack2_x0_3 =	"507800001DAB",
  B_fdouble_add_flags_x0_3 =	"506C00001DAB",
  B_fdouble_sub_flags_x0_3 =	"507C00001DAB",
  B_fdouble_mul_flags_x0_3 =	"507000001DAB",
  B_fdouble_addsub_x0_3 =	"506800001DAB",
  B_fdouble_unpack_min_x0_3 =	"508400001DAB",
  B_fdouble_unpack_max_x0_3 =	"508000001DAB",

  -- Float
  B_fnop_x0_0 =		"514830001",
  B_fnop_x1_0 =		"50D460002",
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

local function parse_imm(imm, bits, shift, scale, signed, slot)
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
  elseif slot == 0 then
    waction("IMM_X0", (signed and 32768 or 0)+scale*1024+bits*32+shift, imm)
    return 0
  else
    waction("IMM_X1", (signed and 32768 or 0)+scale*1024+bits*32+shift, imm)
    return 0
  end
end

local function parse_rbo_x1_imm16(disp, slot)
  local reg, tailr = match(disp, "^([%w_:]+)%s*(.*)$")
  if reg and tailr ~= "" then
    local r, tp = parse_gpr(reg)
    if tp then
      if slot == 0 then
        waction("IMM_X0", 32768+16*32, format(tp.ctypefmt, tailr))
      else
        waction("IMM_X1", 32768+16*32, format(tp.ctypefmt, tailr))
      end
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

local bundle_status = "0"
-- bundle version
map_op[".template__"] = function(params, template, nparams)
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1

  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 2 positions (ins/ext).
  if secpos+2 > maxsecpos and bundle_status == "0" then wflush() end
  local pos = wpos()

  local bundle_flag = sub(template, 9, 9)
  if bundle_flag == "1" or bundle_flag == "4" then
    bundle_status = "1"
  elseif bundle_flag == "2" or bundle_flag == "5" then
    bundle_status = "0"
  end

  -- Process each character.
  for p in gmatch(sub(template, 10), ".") do

    -- X mode
    if p == "A" then
      op = op + shl(parse_gpr(params[n]), 6); n = n + 1
    elseif p == "B" then
      op = op + shl(parse_gpr(params[n]), 12); n = n + 1
    elseif p == "D" then
      op = op + parse_gpr(params[n]); n = n + 1
    elseif p == "L" then
      op = op + shl(parse_gpr(params[n]), 7); n = n + 1
    elseif p == "O" then
      op = op + parse_rbo_x1_imm16(params[n], 1); n = n + 1
    elseif p == "o" then
      op = op + parse_rbo_x1_imm16(params[n], 0); n = n + 1
    elseif p == "G" then
      op = op + shl(parse_imm(params[n], 6, 0, 0, false, 1), 18); n = n + 1
    elseif p == "H" then
      op = op + shl(parse_imm(params[n], 6, 0, 0, false, 1), 12); n = n + 1
    elseif p == "I" then
      op = op + shl(parse_imm(params[n], 16, 0, 0, true, 1), 12); n = n + 1
    elseif p == "i" then
      op = op + shl(parse_imm(params[n], 16, 0, 0, true, 0), 12); n = n + 1
    elseif p == "E" then
      op = op + shl(parse_imm(params[n], 8, 0, 0, true, 1), 12); n = n + 1
    elseif p == "e" then
      op = op + shl(parse_imm(params[n], 8, 0, 0, true, 0), 12); n = n + 1
    elseif p == "z" then -- no relocation support for 'z' yet
      local tmp = parse_imm(params[n], 8, 0, 0, true, 1)
      op = op + band(tmp, 0x3F) + shl(band(shr(tmp, 6), 0x3), 18) ; n = n + 1
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

