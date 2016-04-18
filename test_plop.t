import 'plop'
--
--  See LICENSE
--

local PLOP = require 'ploplib'
PLOP.extend {
  PLOP.std.Cursors,
}
--for k,v in pairs(PLOP) do print(k,v) end

local C = terralib.includecstring [[
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <math.h>
]]

local seed = 1459797014LL--C.time( nil )
print('randseed', seed)
C.srand( seed )

local terra randf() : double return C.rand() / [double](C.RAND_MAX) end

local function test(testname,fn,errstr)
  local errmsg = ''
  print('Executing test... '..testname)
  local success = xpcall(fn, function(errobj)
    errmsg = tostring(errobj)..'\n'..debug.traceback()
  end)
  if not errstr and not success then
    error("Expected test '"..testname.."' to succeed, but it failed:\n"..
          errmsg, 2)
  elseif errstr and success then
    error("Expected test '"..testname.."' to fail, but it succeeded", 2)
  elseif errstr and not string.match(errmsg,errstr) then
    error("Expected test '"..testname.."' to fail, and it did, but for "..
          "the wrong reason:\n"..errmsg, 2)
  end
end

local newlist = terralib.newlist

-------------------------------------------------

test('valid Triangle table layout',function()
  local plop physical Triangles {
    n_tri : size32
    _     : [4]byte
    tris  : {
      v : *[n_tri][3]uint32
      n : *[n_tri][3]float64
      c : *[n_tri]float64
    }
  }

  print(Triangles)
  for k,v in pairs(getmetatable(Triangles._decl)) do print(k,v) end
  print('\nWRAP INSTANCE\n')
  for k,v in pairs(Triangles) do print(k,v) end
  print('\nWRAP\n')
  for k,v in pairs(getmetatable(Triangles)) do print(k,v) end
end)

test('improperly padded Triangle table layout',function()
  local plop physical Triangles {
    n_tri : size32
    tris  : {
      v : *[n_tri][3]uint32
      n : *[n_tri][3]float64
      c : *[n_tri]float64
    }
  }
end, 'required alignment is 8 bytes.*guaranteed to align to 4 bytes')

test('alignment test 1',function()
  local plop physical Synthetic {
    n_vals : size32
         _ : [4]byte
    vals   : [n_vals]float32
    issue  : float64
  }
end, 'required alignment is 8 bytes.*guaranteed to align to 4 bytes')

test('alignment test 2',function()
  local plop physical Synthetic {
    n_vals : size32
    issue  : float64
         _ : uint32
  }
end, 'required alignment is 8 bytes.*guaranteed to align to 4 bytes')

test('ambiguous padding names ok',function()
  local plop physical Synthetic {
    n_vals : size32
         _ : uint32
    issue  : float64
         _ : uint64
  }
end)

test('repeated substruct names',function()
  local plop physical Synthetic {
    a : { b : uint32 }
    a : { c : uint32 }
  }
end, 'cannot have two entries with the same name')

test('ambiguous names not ok',function()
  local plop physical Synthetic {
    a : { b : uint32 }
    b : { a : uint32 }
  }
end, "definition contains ambiguous paths")

test('ambiguous names and shadowing',function()
  local plop physical ShadowAnon {
    n : size32, _:[4]byte
    v : *[n]{
      n : size32
      a : [n]uint32
    }
  }
end, "definition contains ambiguous paths")


test('name re-use',function()
  local plop physical Names {
    xs : {
      n     : size32
      vals  : [n]float32
    }
    ys : {
      n     : size32
      vals  : [n]float32
    }
  }
end)

test('bad alignment triangles',function()
  local plop physical T1 {
    n_tri : size32
    _     : [4]byte
    tris  : *[n_tri]{
      v : [3]uint32
      n : [3]float64
      c : float64
    }
  }
end, 'required alignment is 8 bytes')

test('named constant matrices',function()
  local plop physical V {
    N : size32
    nX = 3
    nY = 3
    _ : [4]byte
    nodes : *[N]{
      m   : [nX][nY]float64
      pos : [3]float64
    }
  }
end)

test('name out of scope',function()
  local plop physical Names {
    xs : {
      n     : size32
      vals  : [n]float32
    }
    ys : {
      vals  : [n]float32
    }
  }
end, "variable 'n' used here was undefined.")

test('valid variation of name struct',function()
  local plop physical Names {
    n : size32
    xs : {
      vals  : [n]float32
    }
    ys : {
      vals  : [n]float32
    }
  }
end)

test('shadowing and arrays',function()
  -- this test very carefully skirts the line of what's ok
  -- since the two ambiguous paths are distinguished by array use
  -- but that is none-the-less considered insufficient
  local plop physical Names {
    n   : size32
    nb  : size32
    xs : {
      a       : *[nb]uint32
      a_vals  : *[n]{
        ny : size64
        ys : {
          a      : *[ny]uint32
          b_vals : *[ny]uint32
        }
      }
    }
  }
end, 'definition contains ambiguous paths')

test('non-randomly-accessible Graph layout',function()
  local plop physical Graph_No_Random {
    n_vert : size32
    verts  : [n_vert] {
      n_neighbors : size32
      neighbors : [n_neighbors]uint32
    }
  }
end, "This plop definition is not randomly accessible")

test('ambiguous names not ok',function()
  local plop physical Synthetic {
    a : { b : uint32 }
    b : { a : uint32 }
  }
end, "definition contains ambiguous paths")


test('valid Triangle programmatic layout',function()
  local Triangles = PLOP.StructOf(
    PLOP.DefOf( 'n_tri', PLOP.PrimOf('size32') ),
    PLOP.DefOf( '_', PLOP.ArrayOf( 4, PLOP.PrimOf('byte') )),
    PLOP.DefOf( 'tris', PLOP.StructOf(
      PLOP.DefOf('v', PLOP.PtrOf(PLOP.ArrayOf(
                      'n_tri', PLOP.ArrayOf(3, PLOP.PrimOf('uint32'))))),
      PLOP.DefOf('n', PLOP.PtrOf(PLOP.ArrayOf(
                      'n_tri', PLOP.ArrayOf(3, PLOP.PrimOf('float64'))))),
      PLOP.DefOf('c', PLOP.PtrOf(PLOP.ArrayOf(
                      'n_tri',PLOP.PrimOf('float64'))))
    ))
  ):compile_physical('Triangles')

  print(Triangles)
end)


test('large test case from rand generator (modified)', function()
  local plop physical Large {
    name_95163 : {
      name_132743 : uint32
      name_89492 = 2
      name_704750 : uint8
                _ : [3]byte
      name_186518 : {
        name_918736 : {
          name_275135 : {
            name_865089 : {
              name_902989 : size16
            }
            name_850464 : size16
                      _ : uint32
            name_194198 : {
              name_847739 : {
                name_769614 : *[name_850464]size64
              }
              name_2725 = 3
              name_870648 : {
                name_565092 : [2][2]uint16
              }
              name_772192 : [2]*{
                name_444247 : *size64
                name_801760 : [name_2725]*{
                  name_424866 : *int32
                  name_943247 : size64
                }
                name_342531 : *uint32
              }
              name_551955 : [name_2725][4]{
                name_684894 : *{
                  name_627811 : ***int16
                }
                name_605724 : *{
                  name_747133 : *size64
                  name_574748 : *[name_89492]*size16
                  name_363946 : *uint8
                  name_396447 : [name_850464]float32
                }
                name_800419 : size64
                name_252259 : float32
                          _ : uint32
              }
            }
          }
          name_257311 = 4
          name_458639 : **size8
          name_345694 : *uint8
          name_676984 = 6
        }
        name_12081 : size8
                 _ : [7]byte
        name_126398 : {
          name_623431 : *[5]uint8
        }
      }
      name_765852 : *size8
      name_583209 : int64
    }
    name_448436 : uint16
  }
end)


local function SplitBuild(name,typ)
  local stuff = PLOP.StructOf(
    PLOP.DefOf( name..'_n1', PLOP.PrimOf('size32') ),
    PLOP.DefOf( '_', PLOP.ArrayOf( 4, PLOP.PrimOf('byte') )),
    PLOP.DefOf( 'vs', PLOP.StructOf(
      PLOP.DefOf(name..'_flags', PLOP.PtrOf(PLOP.ArrayOf(
                      name..'_n1', PLOP.PrimOf('uint8')))),
      PLOP.DefOf(name..'_v1s', PLOP.PtrOf(PLOP.ArrayOf(
                      name..'_n1', typ ))),
      PLOP.DefOf(name..'_v2s', PLOP.PtrOf(PLOP.ArrayOf(
                      name..'_n1', typ )))
    ))
  )
  return stuff
end

test('Large Programmatic Case',function()
  local Arrs = SplitBuild
  local tree =
    Arrs('a', Arrs('b', Arrs('c', Arrs('d',
      --Arrs('e', Arrs('f', Arrs('g', Arrs('h',
        PLOP.PrimOf('float32')
      --))))
    ))))
  local t0 = terralib.currenttimeinseconds()
  tree:compile_physical()
  print('  took (sec) '..(terralib.currenttimeinseconds()-t0))
end)

-- some off the cuff measurements of the above
--   0 = 220 ms
-- 2^4 = 380 ms  160
-- 2^5 = 520 ms  300
-- 2^6 = 850 ms  630
-- 2^7 = 1600 ms 1380
-- 2^8 = 3400 ms 3180
-- this suggests a slightly above linear increase with this kind of
-- structure growth, which isn't too bad, especially given that we
-- know there are quadratic sub-computations.

-------------------------------------------------------------------------------
-- logical layouts
-------------------------------------------------------------------------------

test('logical triangles',function()
  local plop logical Triangles {
    n_tri : size
    tris  : [n_tri] {
      v : [3]uint
      n : [3]float
      c : float
    }
  }

  print(Triangles)
end)

test('Triangles subtypes',function()
  local plop logical Triangles {
    n_tri : size
    tris  : [n_tri] {
      v : [3]uint
      n : [3]float
      c : float
    }
  }

  local plop physical T1 {
    n_tri : size32
        _ : [4]byte
    tris  : [n_tri] {
      v : [3]uint32
      _ : [4]byte
      n : [3]float64
      c : float64
    }
  }
  assert(T1:subtype_of(Triangles))

  local plop physical T2 {
    n_tri = 3752
    tris  : [n_tri] {
      v : [3]uint32
      _ : [4]byte
      n : [3]float64
      c : float64
    }
  }
  assert(T2:subtype_of(Triangles))

  local plop physical T3 {
    n_tri : size32
    _     : [4]byte
    tris  : *{
      v : [n_tri][3]uint32
      n : [n_tri][3]float64
      c : [n_tri]float64
    }
  }
  assert(T3:subtype_of(Triangles))

  local plop physical T4 {
    n_tri : size32
    _     : [4]byte
    tris  : {
      v : *[n_tri][3]uint32
      n : *[n_tri][3]float64
      c : *[n_tri]float64
    }
  }
  assert(T4:subtype_of(Triangles))

  local plop physical T5 {
    n_tri : size32
    _     : [4]byte
    tris  : {
      v : [3] * [n_tri]uint32
      n : [3] * [n_tri]float64
      c : * [n_tri]float64
    }
  }
  assert(T5:subtype_of(Triangles))

  assert(T5:equals(T1))
end)


test('Programmatic Equality',function()
  local function Arrs(name,typ)
    return PLOP.StructOf(
      PLOP.DefOf(name..'_v1s', PLOP.PtrOf(PLOP.ArrayOf( 'n', typ ))),
      PLOP.DefOf(name..'_v2s', PLOP.PtrOf(PLOP.ArrayOf( 'n', typ )))
    )
  end
  local f32 = PLOP.PrimOf('float32')
  local tree1 = PLOP.StructOf(
    PLOP.DefOf( 'n', PLOP.PrimOf('size64')),
    PLOP.DefOf('data', Arrs('a', Arrs('b', Arrs('c', f32 ))))
  )
  local tree2 = PLOP.StructOf(
    PLOP.DefOf( 'n', PLOP.PrimOf('size64')),
    PLOP.DefOf('data', Arrs('b', Arrs('a', Arrs('c', f32 ))))
  )
  local tree3 = PLOP.StructOf(
    PLOP.DefOf( 'n', PLOP.PrimOf('size64')),
    PLOP.DefOf('data', Arrs('c', Arrs('b', Arrs('a', f32 ))))
  )
  tree1 = tree1:compile_physical()
  tree2 = tree2:compile_physical()
  tree3 = tree3:compile_physical()
  assert(tree1:equals(tree2))  assert(tree2:equals(tree1))
  assert(tree2:equals(tree3))  assert(tree3:equals(tree2))
  assert(tree3:equals(tree1))  assert(tree1:equals(tree3))
end)

test('Graph layouts',function()
  local plop logical GraphL {
    n_vert : size32
    verts  : [n_vert] {
      n_neighbors : size32
      neighbors   : [n_neighbors]uint32
    }
  }
  
  local plop physical GraphP {
    n_vert : size32
         _ : [4]byte
    verts  : [n_vert] * {
      n_neighbors : size32
      neighbors   : [n_neighbors]uint32
    }
  }

  local plop physical GraphP2 {
    n_vert : size32
         _ : [4]byte
    verts  : [n_vert] {
      n_neighbors : size32
                _ : [4]byte
      neighbors   : *[n_neighbors]uint32
    }
  }

  assert(GraphP:subtype_of(GraphL))
  assert(GraphP2:subtype_of(GraphL))
end)


test('Logical Graph Specialization',function()
  local plop logical GraphL {
    n_vert : size32
    verts  : [n_vert] {
      n_neighbors : size32
      neighbors   : [n_neighbors]uint32
    }
  }
  
  local plop physical GraphP1 {
    n_vert : size32
         _ : [4]byte
    verts  : [n_vert] * {
      n_neighbors : size32
      neighbors   : [n_neighbors]uint32
    }
  }

  local plop physical GraphP2 {
    n_vert : size32
         _ : [4]byte
    verts  : [n_vert] {
      n_neighbors : size32
                _ : [4]byte
      neighbors   : *[n_neighbors]uint32
    }
  }

  local Graph1 = GraphL(GraphP1)
  local Graph2 = GraphL(GraphP2)
end)




-------------------------------------------------------------------------------
-- Physical Cursors
-------------------------------------------------------------------------------

test('cursor test',function()
  local plop physical Triangles {
    n_tri : size32
    _     : [4]byte
    tris  : {
      v : *[n_tri][3]uint32
      n : *[n_tri][3]float64
      c : *[n_tri]float64
    }
  }

  for k=1,1 do
    local Tcursor = Triangles:cursor()
    local terra do_test()
      var c = Tcursor.alloc(C.malloc)
      c.n_tri = 35
      var tris = c.tris -- this is an issue
                        -- if I remove this line then some extra
                        -- index-arithmetic gets generated
                        -- THIS IS BECAUSE the compiler cannot determine
                        -- that the SIZE value is constant
      tris.v:alloc(C.malloc)
      tris.n:alloc(C.malloc)
      tris.c:alloc(C.malloc)
      var n = tris.n(8)
      n(1) = 0.13245
      tris.v:free(C.free)
      tris.n:free(C.free)
      tris.c:free(C.free)
      Tcursor.free(c, C.free)
    end
    --do_test:disas()
    for k=1,2e1 do
      do_test()
    end
  end

  local struct arrptrs {
    v : &(uint32[3])
    n : &(double[3])
    c : &double
  }
  local struct TTri {
    n_tri : uint32
        _ : uint32
    tris : arrptrs
  }
  for k=1,1 do
    local terra baseline()
      var ts = [&TTri](C.malloc(sizeof(TTri)))
      ts.n_tri = 35
      ts.tris.v = [&(uint32[3])](C.malloc(sizeof([ uint32[3] ])*35))
      ts.tris.n = [&(double[3])](C.malloc(sizeof([ double[3] ])*35))
      ts.tris.c = [&double](C.malloc(sizeof(double)*35))
      var n = &(ts.tris.n[8])
      (@n)[1] = 0.13245
      C.free(ts.tris.v)
      C.free(ts.tris.n)
      C.free(ts.tris.c)
      C.free(ts)
    end
    --baseline:disas()
    for k=1,2e1 do
      baseline()
    end
  end
end)

test('graph cursor test',function()
  local plop physical GraphP {
    n_vert : size32
         _ : [4]byte
    verts  : [n_vert] * {
      val1        : float64
      val2        : float64
      n_neighbors : size32
      neighbors   : [n_neighbors]uint32
    }
  }
  -- allocate the graph randomly
  local terra rand_tail( n : uint )
    var roll  : double = C.rand() / [double](C.RAND_MAX)
    var recip : double = 1.0 / (roll*roll)
    var val   : uint   = [uint](recip)%n
    return val
  end
  local terra alloc_init_graph()
    var nv    = 1000000
    var c     = GraphP.alloc(C.malloc, nv)
    c.n_vert  = nv
    for i=0,nv do
      var nn = rand_tail(30)
      c.verts(i):alloc(C.malloc, nn)
      c.verts(i).n_neighbors = nn
      c.verts(i).val1 = randf()
      c.verts(i).val2 = randf()
      for j=0,nn do c.verts(i).neighbors(j) = C.rand() % nv end
    end
    return c
  end
  local terra free_graph( c : GraphP:cursor() ) c:free_all(C.free) end

  local terra graph_diffuse( g : GraphP:cursor() )
    var nv = g.n_vert
    var vs = g.verts
    for k=0,nv do
      var v     = vs(k)
      var sum   = 0.0
      var nn    = v.n_neighbors
      for i=0,nn do
        sum = sum + vs( v.neighbors(i) ).val1
      end
      v.val2 = v.val2 + 0.4*(sum / nn - v.val2)
    end
    for k=0,nv do
      var v     = vs(k)
      var sum   = 0.0
      var nn    = v.n_neighbors
      for i=0,nn do
        sum = sum + vs( v.neighbors(i) ).val2
      end
      v.val1 = v.val1 + 0.4*(sum / nn - v.val1)
    end
  end

  local struct VVals { val1 : double, val2 : double, nn : uint32 }
  local terra graph_manual_diffuse( g : GraphP:cursor() )
    var nv = g.n_vert
    var vs = [&&VVals](g.verts:ptr())
    for k=0,nv do
      var v     = vs[k]
      var v2    = v.val2
      var nn    = v.nn
      var sum   = 0.0
      var ns    = [&uint32]([&uint8](v)+20)
      for i=0,nn do
        sum = sum + vs[ ns[i] ].val1
      end
      vs[k].val2 = v2 + 0.4*(sum / nn - v2)
    end
    for k=0,nv do
      var v     = vs[k]
      var v1    = v.val1
      var nn    = v.nn
      var sum   = 0.0
      var ns    = [&uint32]([&uint8](v)+20)
      for i=0,nn do
        sum = sum + vs[ ns[i] ].val2
      end
      v.val1 = v1 + 0.4*(sum / nn - v1)
    end
  end
  graph_diffuse:compile()
  graph_manual_diffuse:compile()
  --graph_diffuse:disas()
  --print('woooo\n\n\n\n\n\n\n')
  --graph_manual_diffuse:disas()


  local graph = alloc_init_graph()
  local t1 = terralib.currenttimeinseconds()
  for k=1,2 do graph_diffuse(graph) end
  local t2 = terralib.currenttimeinseconds()
  for k=1,2 do graph_manual_diffuse(graph) end
  local t3 = terralib.currenttimeinseconds()
  free_graph(graph)

  local cursortime = t2-t1
  local manualtime = t3-t2

  print('cursor (sec)', t2-t1)
  print('manual (sec)', t3-t2)

  assert( cursortime*0.9 < manualtime and manualtime < cursortime*1.1 )

end)



test('grid cursor test',function()
  local plop physical GridP {
    nx : size32
    ny : size32
    nz : size32
     _ : size32
    cells : {
      vel   : *[nx][ny][nz][3]float32
      prev  : *[nx][ny][nz][3]float32
    }
  }
  local NX,NY,NZ = 64,64,64
  local terra alloc_init_grid()
    var c             = GridP.alloc(C.malloc)
    c.nx, c.ny, c.nz  = NX, NY, NZ
    c.cells.vel:alloc(C.malloc)
    c.cells.prev:alloc(C.malloc)
    var vel = c.cells.vel()
    var prev = c.cells.prev()
    for i=0,NX do for j=0,NY do for k=0,NZ do
      for d=0,3 do
        vel(i)(j)(k)(d) = randf()
      end
    end end end
    return c
  end
  local terra grid_copy( dst : GridP:cursor(), src : GridP:cursor() )
    var nx, ny, nz = src.nx, src.ny, src.nz
    for i=0,nx do for j=0,ny do for k=0,nz do
      for d=0,3 do
        dst.cells.vel(i)(j)(k)(d)   = src.cells.vel(i)(j)(k)(d)
        dst.cells.prev(i)(j)(k)(d)  = src.cells.prev(i)(j)(k)(d)
      end
    end end end
  end
  local terra check_grid_eq( dst : GridP:cursor(), src : GridP:cursor() )
    var nx, ny, nz = src.nx, src.ny, src.nz
    for i=0,nx do for j=0,ny do for k=0,nz do
      for d=0,3 do
        if dst.cells.vel(i)(j)(k)(d) ~= src.cells.vel(i)(j)(k)(d)
        or dst.cells.prev(i)(j)(k)(d) ~= src.cells.prev(i)(j)(k)(d)
        then return false end
      end
    end end end
    return true
  end
  local terra free_grid( c : GridP:cursor() ) c:free_all(C.free) end
  local terra swapbuf( c : GridP:cursor() )
    var tmp = @(c.cells.vel:ptr())
    @(c.cells.vel:ptr()) = @(c.cells.prev:ptr())
    @(c.cells.prev:ptr()) = tmp
  end

  local terra grid_diffuse( g : GridP:cursor() )
    var nx, ny, nz = g.nx, g.ny, g.nz
    var vel = g.cells.vel()
    var prev = g.cells.prev()
    for i=1,nx-1 do for j=1,ny-1 do for k=1,nz-1 do
      for d=0,3 do
        vel(i)(j)(k)(d) = 0.6*prev(i)(j)(k)(d)
          + 0.4*(1/6.0)*( prev(i-1)(j)(k)(d) + prev(i+1)(j)(k)(d)
                        + prev(i)(j-1)(k)(d) + prev(i)(j+1)(k)(d)
                        + prev(i)(j)(k-1)(d) + prev(i)(j)(k+1)(d) )
      end
    end end end
  end

  local struct GridT {
    nx      : uint32
    ny      : uint32
    nz      : uint32
    padding : uint32
    vel     : &float
    prev    : &float
  }

  local idx = macro(function(i,j,k,d,ny,nz)
    return `i*ny*nz*3 + j*nz*3 + k*3 + d
  end)
  local terra grid_manual_diffuse( gc : GridP:cursor() )
    var g = @[&GridT](gc:ptr())
    var nx, ny, nz = g.nx, g.ny, g.nz
    var vel   = g.vel
    var prev  = g.prev
    for i=1,nx-1 do for j=1,ny-1 do for k=1,nz-1 do
      for d=0,3 do
        vel[idx(i,j,k,d,ny,nz)] = 0.6 * prev[idx(i,j,k,d,ny,nz)]
          + 0.4*(1/6.0)*(
              prev[idx(i-1,j,k,d,ny,nz)] + prev[idx(i+1,j,k,d,ny,nz)]
            + prev[idx(i,j-1,k,d,ny,nz)] + prev[idx(i,j+1,k,d,ny,nz)]
            + prev[idx(i,j,k-1,d,ny,nz)] + prev[idx(i,j,k+1,d,ny,nz)])
      end
    end end end
  end
  grid_diffuse:compile()
  grid_manual_diffuse:compile()
  --grid_diffuse:disas()
  --print('woooo\n\n\n\n\n\n\n')
  --grid_manual_diffuse:disas()


  local grid = alloc_init_grid()
  local grid2 = alloc_init_grid()
  grid_copy(grid2, grid)
  assert(check_grid_eq(grid, grid2))
  local t1 = terralib.currenttimeinseconds()
  for k=1,5e2 do swapbuf(grid); grid_diffuse(grid) end
  local t2 = terralib.currenttimeinseconds()
  for k=1,5e2 do swapbuf(grid2); grid_manual_diffuse(grid2) end
  local t3 = terralib.currenttimeinseconds()
  assert(check_grid_eq(grid, grid2))
  free_grid(grid)
  free_grid(grid2)

  local cursortime = t2-t1
  local manualtime = t3-t2

  print('cursor (sec)', t2-t1)
  print('manual (sec)', t3-t2)

  assert( cursortime*0.9 < manualtime )
  -- cursor appears to be significantly faster

end)


-------------------------------------------------------------------------------
-- Logical Cursors
-------------------------------------------------------------------------------

test('Logical Cursor Triangle Test',function()
  local plop logical Triangles {
    n_tri : size
    tris  : [n_tri]{
      v : [3]uint
      n : [3]float
      c : float
    }
  }

  local plop physical Vertices {
    n   : size32
    _   : [4]byte
    pos : *[n][3]float64
  }

  local plop physical T1 {
    n_tri : size32
    _     : [4]byte
    tris  : *[n_tri]{
      v : [3]uint32
      _ : uint32
      n : [3]float64
      c : float64
    }
  }

  local plop physical T2 {
    n_tri : size32
    _     : [4]byte
    tris  : {
      v : *[3][n_tri]uint32
      n : *[3][n_tri]float64
      c : *[n_tri]float64
    }
  }

  local Tris1 = Triangles(T1)
  local Tris2 = Triangles(T2)

  local terra do_alloc_1( n : uint32 )
    var c = T1.alloc(C.malloc)
    c.n_tri = n
    c.tris:alloc(C.malloc)
    return Tris1.New(c)
  end
  local terra free_alloc_1( lc : Tris1:cursor() ) lc:free_all(C.free) end
  local terra do_alloc_2( n : uint32 )
    var c = T2.alloc(C.malloc)
    c.n_tri = n
    c.tris.v:alloc(C.malloc)
    c.tris.n:alloc(C.malloc)
    c.tris.c:alloc(C.malloc)
    return Tris2.New(c)
  end
  local terra free_alloc_2( lc : Tris2:cursor() ) lc:free_all(C.free) end
  local terra alloc_verts( n : uint32 )
    var c = Vertices.alloc(C.malloc)
    c.n = n
    c.pos:alloc(C.malloc)
    return c
  end
  local terra free_verts( c : Vertices:cursor() ) c:free_all(C.free) end

  local terra init_verts( c : Vertices:cursor() )
    for k=0,c.n do
      for d=0,3 do c.pos(k)(d) = randf() end
    end
  end
  local function init_tris( Layout )
    return terra( c : Layout:cursor(), vc : Vertices:cursor() )
      var n_v = vc.n
      for i = 0,c.n_tri do
        var tri = c.tris(i)
        for k=0,3 do tri.v(k) = C.rand() % n_v end
        for k=0,3 do tri.n(k) = 0.0 end
      end
    end
  end

  local function copy_verts(Layout1,Layout2, c1, c2)
    local terra do_check( c1 : Layout1:cursor(), c2 : Layout2:cursor() )
      return c1.n_tri == c2.n_tri
    end
    if not do_check(c1,c2) then error('number of triangles does not match') end
    local terra do_copy( c1 : Layout1:cursor(), c2 : Layout2:cursor() )
      var n_t   = c1.n_tri
      for i=0,n_t do
        var t1 = c1.tris(i)
        var t2 = c2.tris(i)
        for k=0,3 do t1.v(k) = t2.v(k) end
      end
    end
    do_copy(c1,c2)
  end

  local function check_normals(Layout1,Layout2, c1, c2)
    local terra do_check( c1 : Layout1:cursor(), c2 : Layout2:cursor() )
      return c1.n_tri == c2.n_tri
    end
    if not do_check(c1,c2) then
      error('number of triangles does not match')
    end
    local terra normal_check( c1 : Layout1:cursor(), c2 : Layout2:cursor() )
      var n_t   = c1.n_tri
      for i=0,n_t do
        var t1 = c1.tris(i)
        var t2 = c2.tris(i)
        for k=0,3 do if t1.n(k) ~= t2.n(k) then return false end end
      end
      return true
    end
    return normal_check(c1,c2)
  end

  local function do_test(Layout, tc, vc, str)
    local terra compute_normals( tc:Layout:cursor(), vc:Vertices:cursor() )
      var n_t   = tc.n_tri
      var vpos  = vc.pos() -- deref pointer
      for i=0,n_t do
        var t = tc.tris(i)
        var v0, v1, v2 = t.v(0), t.v(1), t.v(2)
        var v0x, v0y, v0z = vpos(v0)(0), vpos(v0)(1), vpos(v0)(2)
        var v1x, v1y, v1z = vpos(v1)(0), vpos(v1)(1), vpos(v1)(2)
        var v2x, v2y, v2z = vpos(v2)(0), vpos(v2)(1), vpos(v2)(2)
        var nx =  (v1x-v0x) * (v2y-v0y) - (v1y-v0y) * (v2x-v0x)
        var ny = -(v1x-v0x) * (v2z-v0z) + (v1z-v0z) * (v2x-v0x)
        var nz =  (v1y-v0y) * (v2z-v0z) - (v1z-v0z) * (v2y-v0y)
        t.n(0), t.n(1), t.n(2) = nx, ny, nz
      end
    end
    compute_normals:compile()

    local t0 = terralib.currenttimeinseconds()
    for k=1,2e3 do
      compute_normals(tc, vc)
    end
    local t1 = terralib.currenttimeinseconds()
    print(str, t1-t0)
    return t1-t0
  end

  local tc1 = do_alloc_1(5e4)
  local tc2 = do_alloc_2(5e4)
  local vc  = alloc_verts(3e4); init_verts(vc)
  init_tris(Tris1)(tc1, vc)
  init_tris(Tris2)(tc2, vc)
  copy_verts(Tris1,Tris2,tc1,tc2)

  local t1 = do_test(Tris1, tc1, vc, "time for layout 1: ")
  local t2 = do_test(Tris2, tc2, vc, "time for layout 2: ")
  assert(0.9*t2 < t1)  -- layout 2 may be faster or about the same

  assert(check_normals(Tris1,Tris2,tc1,tc2))
  free_alloc_1(tc1)
  free_alloc_2(tc2)
end)

test('Logical Grid Cursor Test',function()
  local plop logical GridL {
    nx : size
    ny : size
    nz : size
    cells : [nx][ny][nz]{
      vel   : [3]float32
      prev  : [3]float32
    }
  }
  
  local plop physical GridP1 {
    nx : size32
    ny : size32
    nz : size32
     _ : [4]byte
    cells : {
      vel   : *[nx][ny][nz][3]float32
      prev  : *[nx][ny][nz][3]float32
    }
  }

  local plop physical GridP2 {
    nx : size32
    ny : size32
    nz : size32
     _ : [4]byte
    cells : {
      vel   : *[nz][ny][nx][3]float32
      prev  : *[nz][ny][nx][3]float32
    }
  }

  local Grid1 = GridL(GridP1)
  local Grid2 = GridL(GridP2)

  local NX,NY,NZ = 64,64,64
  local terra alloc_grid1()
    var c             = GridP1.alloc(C.malloc)
    c.nx, c.ny, c.nz  = NX, NY, NZ
    c.cells.vel:alloc(C.malloc)
    c.cells.prev:alloc(C.malloc)
    return Grid1.New(c)
  end
  local terra alloc_grid2()
    var c             = GridP2.alloc(C.malloc)
    c.nx, c.ny, c.nz  = NX, NY, NZ
    c.cells.vel:alloc(C.malloc)
    c.cells.prev:alloc(C.malloc)
    return Grid2.New(c)
  end
  local terra free_grid1( g : Grid1:cursor() ) g:free_all(C.free) end
  local terra free_grid2( g : Grid2:cursor() ) g:free_all(C.free) end
  local function init_grid(Layout, g)
    local terra init( g : Layout:cursor() )
      var nx, ny, nz = g.nx, g.ny, g.nz
      for i=0,nx do for j=0,ny do for k=0,nz do
        for d=0,3 do g.cells(i)(j)(k).vel(d) = randf() end
      end end end
    end
    init(g)
  end

  local terra swapbuf1( g : Grid1:cursor() )
    var c = g:physical_cursor()
    var tmp = @(c.cells.vel:ptr())
    @(c.cells.vel:ptr()) = @(c.cells.prev:ptr())
    @(c.cells.prev:ptr()) = tmp
  end
  local terra swapbuf2( g : Grid2:cursor() )
    var c = g:physical_cursor()
    var tmp = @(c.cells.vel:ptr())
    @(c.cells.vel:ptr()) = @(c.cells.prev:ptr())
    @(c.cells.prev:ptr()) = tmp
  end

  local function grid_copy( dst, src, DstLayout, SrcLayout )
    local terra copy( dst : DstLayout:cursor(), src : SrcLayout:cursor() )
      var nx, ny, nz = src.nx, src.ny, src.nz
      for i=0,nx do for j=0,ny do for k=0,nz do
        var dc, sc  = dst.cells(i)(j)(k), src.cells(i)(j)(k)
        for d=0,3 do
          dc.vel(d)   = sc.vel(d)
          dc.prev(d)  = sc.prev(d)
        end
      end end end
    end
    copy(dst,src)
  end
  local function check_grid_eq( dst, src, DstLayout, SrcLayout )
    local terra check( dst : DstLayout:cursor(), src : SrcLayout:cursor() )
      var nx, ny, nz = src.nx, src.ny, src.nz
      for i=0,nx do for j=0,ny do for k=0,nz do
        for d=0,3 do
          var dc, sc  = dst.cells(i)(j)(k), src.cells(i)(j)(k)
          if dc.vel(d)  ~= sc.vel(d) or dc.prev(d) ~= sc.prev(d)
          then return false end
        end
      end end end
      return true
    end
    return check(dst,src)
  end

  local function do_test( g, Grid, swap, str )
    local terra diffusion( g : Grid:cursor() )
      var nx, ny, nz = g.nx, g.ny, g.nz
      for i=1,nx-1 do for j=1,ny-1 do for k=1,nz-1 do
        var cs = g.cells
        for d=0,3 do
          cs(i)(j)(k).vel(d) = 0.6*cs(i)(j)(k).prev(d)
            + 0.4*(1/6.0)*( cs(i-1)(j)(k).prev(d) + cs(i+1)(j)(k).prev(d)
                          + cs(i)(j-1)(k).prev(d) + cs(i)(j+1)(k).prev(d)
                          + cs(i)(j)(k-1).prev(d) + cs(i)(j)(k+1).prev(d) )
        end
      end end end
    end
    diffusion:compile()

    local t0 = terralib.currenttimeinseconds()
    for k=1,2e2 do
      swap(g)
      diffusion(g)
    end
    local t1 = terralib.currenttimeinseconds()
    print(str, t1-t0)
    return t1-t0
  end

  local g1 = alloc_grid1()
  local g2 = alloc_grid2()
  init_grid(Grid1,g1)
  grid_copy(g2, g1, Grid2, Grid1)

  local t1 = do_test(g1, Grid1, swapbuf1, 'grid layout 1: ')
  local t2 = do_test(g2, Grid2, swapbuf2, 'grid layout 2: ')
  assert(t1 < 0.9*t2) -- should be faster to not iterate wrong

  assert(check_grid_eq(g2, g1, Grid2, Grid1))
  free_grid1(g1)
  free_grid2(g2)
end)

local function blah()

  local function memoize_from(idx,f)
    local cache = {}
    local function memoization_wrapper(...)
      local args     = {select(idx,...)}
      local subcache = cache
      for i=1,#args do
        local sub = subcache[nilconvert(args[i])]
        if not sub then
          sub = {}
          subcache[nilconvert(args[i])] = sub
        end
        subcache = sub
      end
      local lookup = subcache[lookuptoken]
      if not lookup then
        lookup = f(...)
        subcache[lookuptoken] = lookup
      end
      return lookup
    end
    return memoization_wrapper
  end
  local function memoize(f)
    return memoize_from(1,f)
  end

  local function template(func)
    local memofunc = memoize(func)
    return macro(function(...)
      -- convert args to types
      local typs = newlist()
      local N = select('#',...)
      for i=1,N do typs:insert( select(i,...):gettype() ) end
      -- get specialization
      local f = memofunc(unpack(typs))
      return `f([...])
    end,function(...)
      -- convert args to types
      local typs = newlist()
      local N = select('#',...)
      for i=1,N do
        local a = select(i,...)
        local t = type(a)
        if t == 'cdata' then t = terralib.typeof(t) end
        typs:insert(t)
      end
      -- get specialization
      local f = memofunc(unpack(typs))
      return f(...)
    end)
  end

  -- could improve yet more...
  local check_grids = template(function(Type1, Type2)
    -- Do typechecking here
    return terra( a : Type1, b : Type2, c : double )
      -- something
    end
  end)

  local build_terra_func = memoize(function( DstCursor, SrcCursor )
    if not PLOP.is_cursor(DstCursor)
    or not PLOP.is_cursor(SrcCursor) then
      error('expected two cursor arguments')
    end
    return terra( dst : DstCursor, src : SrcCursor )
      var nx, ny, nz = src.nx, src.ny, src.nz
      for i=0,nx do for j=0,ny do for k=0,nz do
        for d=0,3 do
          var dc, sc  = dst.cells(i)(j)(k), src.cells(i)(j)(k)
          if dc.vel(d)  ~= sc.vel(d) or dc.prev(d) ~= sc.prev(d)
          then return false end
        end
      end end end
      return true
    end
  end)
  local macro_wrap = macro(function( dst, src ) -- terra
    local dt, st = dst:gettype(), src:gettype()
    local f = build_terra_func(dt,st)
    return `f(dst,src)
  end, function( dst, src ) -- lua
    local dt = type(dst) == 'cdata' and terralib.typeof(dst)
    local st = type(src) == 'cdata' and terralib.typeof(src)
    local f = build_terra_func(dt,st)
    return f(dst,src)
  end)

  local terra testmacro( d : Grid2:cursor(), s : Grid1:cursor() )
    check_grid_eq(d,s)
  end
end


-------------------------------------------------------------------------------
-- random Layout generator  For Fuzzing
-------------------------------------------------------------------------------

-- discrete probability distribution
local function distribution(proportions)
  local N = #proportions
  local presums = {}
  local total = 0
  for i,p in ipairs(proportions) do
    total = total + p
    presums[i] = total
  end
  local cutoffs = { 0 }
  for i,p in ipairs(presums) do
    cutoffs[i+1] = p / total
  end
  return function()
    local roll = math.random()
    local k = 1
    while k <= N do
      if ceilings[k] < roll and roll < ceilings[k+1] then
        return k
      end
    end
  end
end

local function rand_draw(xs)
  local roll = math.floor(math.random()*(#xs)) + 1
  return xs[roll]
end
local function rand_remove(xs)
  local roll = math.floor(math.random()*(#xs)) + 1
  return table.remove(xs, roll)
end

local rand_pdecl

local function rand_name()
  return 'name_'..tostring(math.floor(math.random()*1e6))
end
local function rand_size()
  return math.floor(math.random()*5) + 2
end
local pprim_list = {
  "size8", "size16", "size32", "size64",
  "uint8", "uint16", "uint32", "uint64",
  "int8", "int16", "int32", "int64",
  "float32", "float64", "byte",
}
local function rand_pprim()
  return PLOP.PrimOf( rand_draw(pprim_list) ) end
local sizeprim_list = { "size8", "size16", "size32", "size64" }
local function rand_sizeprim()
  return PLOP.PrimOf( rand_draw(sizeprim_list) ) end


local function rand_ptr(names)
  local typ, names = rand_pdecl(names)
  return PLOP.PtrOf(typ)
end

local function rand_array(names)
  local typ = rand_pdecl(names)
  local size = nil
  if #names > 0 and math.random() > 0.5 then size = rand_draw(names)
                                        else size = rand_size() end
  return PLOP.ArrayOf(size, typ)
end

local avg_entries = 2
local p_geom = 1/avg_entries
local function geom_num()
  local k = 0
  repeat
    k=k+1
    local roll = math.random()
  until roll < p_geom
  return k
end
local size_def_prob = 0.3
local function rand_struct(names)
  names = names and newlist{ unpack(names) } or newlist()
  local entries = newlist()
  local n_entries = geom_num()
  for k=1,n_entries do
    do
      local field_name = rand_name()
      local typ   = rand_pdecl(names)
      entries:insert(PLOP.DefOf(field_name, typ))
    end
    if math.random() < size_def_prob then
      local size_name = rand_name()
      names:insert(size_name)
      if math.random() > 0.5 then
        entries:insert(PLOP.DefOf(size_name, rand_sizeprim()))
      else
        entries:insert(PLOP.ConstOf(size_name, rand_size()))
      end
    end
  end
  return PLOP.StructOf(unpack(entries))
end

function rand_pdecl(names)
  local case = rand_draw({1,1,1,1,1,1,2,2,2,3,3,3,4,4,4})
  if      case == 1 then
    return rand_pprim()
  elseif  case == 2 then
    return rand_ptr(names)
  elseif  case == 3 then
    return rand_array(names)
  else
    return rand_struct(names)
  end
end

--local seed = math.floor(terralib.currenttimeinseconds() % 5 * 1e6)
--print('rand seed', seed)
--math.randomseed(seed)
--for k=1,5 do 
--  local decl = rand_struct():compile_layout('RandLayout')
--  print(decl)
--  print('SUCCESS')
--end

