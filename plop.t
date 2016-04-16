--[[
  plop - A Small Langauge for abstracting over byte-by-byte details of
          physical layout
    
    by Gilbert Bernstein
    March 2016
    
  See LICENSE
--]]

local PLOP = require 'plop_core'

local blocklist = { 
  parse           = true,
  typecheck       = true,
  wrap_physical   = true,
  wrap_logical    = true,
}
local exports = {}
for k,v in pairs(PLOP) do
  if not blocklist[k] then exports[k] = v end
end
package.loaded['ploplib'] = exports
exports.std = {}
local CURSORS = require 'plop_cursors'
exports.std.Cursors   = CURSORS.Cursors
exports.std.is_cursor = CURSORS.is_cursor

local function infer_layout(decl)
  if decl:is_logical() then
    if decl:is_physical() then
      error('could not infer whether layout was logical or physical;'..
            'please annotate', 3)
    end
    return 'logical'
  elseif decl:is_physical() then
    return 'physical'
  else
    error('layout mixes physical features (i.e. pointers) and '..
          'logical features (i.e. un-sized primitives); it is not '..
          'ok to use this layout logically nor physically', 3)
  end
end

local function commonExprStmt(self, layout_type, lexer, name)
  local decl = PLOP.parse(lexer)

  local function constructor(env_fn)
    PLOP.typecheck(decl)

    if not layout_type then layout_type = infer_layout(decl) end
    
    if layout_type == 'physical' then
      return PLOP.wrap_physical(decl, name)
    elseif layout_type == 'logical' then
      return PLOP.wrap_logical(decl, name)
    end
  end

  return constructor
end
local function handleExpression(self, lexer)
  lexer:expect('plop')

  local layout_type = nil
  if      lexer:nextif('logical')   then layout_type = 'logical'
  elseif  lexer:nextif('physical')  then layout_type = 'physical' end

  return commonExprStmt(self, layout_type, lexer)
end
local function handleStatement(self, lexer)
  lexer:expect('plop')

  local layout_type = nil
  if      lexer:nextif('logical')   then layout_type = 'logical'
  elseif  lexer:nextif('physical')  then layout_type = 'physical' end

  local typname = lexer:expect(lexer.name).value
  local assigntuple = { typname }

  return commonExprStmt(self, layout_type, lexer, typname), assigntuple
end

local plop_language = {
  name          = 'plop_langauge',
  entrypoints   = {'plop'},
  keywords      = {'physical','logical'},

  expression      = handleExpression,
  statement       = handleStatement,
  localstatement  = handleStatement,
}

return plop_language