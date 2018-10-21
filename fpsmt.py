# This is free and unencumbered software released into the public domain.

# Anyone is free to copy, modify, publish, use, compile, sell, or
# distribute this software, either in source code form or as a compiled
# binary, for any purpose, commercial or non-commercial, and by any
# means.

# In jurisdictions that recognize copyright laws, the author or authors
# of this software dedicate any and all copyright interest in the
# software to the public domain. We make this dedication for the benefit
# of the public at large and to the detriment of our heirs and
# successors. We intend this dedication to be an overt act of
# relinquishment in perpetuity of all present and future rights to this
# software under copyright law.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
# IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
# OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
# ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.

# For more information, please refer to <http://unlicense.org>

from pprint import pprint

N = 0
def gensym():
  global N
  N += 1
  return "var{}".format(N)

def bv(width):
  return "(_ BitVec {})".format(width)

def bvadd(a, b):
  return "(bvadd {} {})".format(a,b)

def bvsub(a, b):
  return "(bvadd {} {})".format(a,b)

def bvmul(a, b):
  return "(bvmul {} {})".format(a,b)

def zeroext(name, size):
  return "((_ zero_extend {}) {})".format(size, name)

def extract(hi, lo, expr):
  return "((_ extract {} {}) {})".format(hi, lo, expr)

def bvuge(a, b):
  return "(bvuge {} {})".format(a,b)

def bvlte(a, b):
  return "(bvlte {} {})".format(a,b)

def bvlt(a, b):
  return "(bvlt {} {})".format(a,b)

def bvgt(a, b):
  return "(bvgt {} {})".format(a,b)

def smtassert(expr):
  return "(assert {})".format(expr)

def clamp(result, bits):
  max = bvconst(2**(bits-1)-1, bits)
  return ite(bvuge(result, max), max, result)

def ite(cond, a, b):
  return "(ite {} {} {})".format(cond, a, b)

def bvconst(i, bits):
  return "(_ bv{} {})".format(i, bits)

def decl(name, sort):
  return "(declare-const {} {})".format(name, sort)

def equals(a, b):
  return "(assert (= {} {}))".format(a,b)

class fp:
  __vars = []
  
  def __init__(self, name, ib, fb, rnd = None, log = True):
    self.name = name
    self.ib = ib
    self.fb = fb
    self.size = ib + fb
    self.rnd = rnd
    if log:
      fp.__vars.append(decl(self.name, bv(ib + fb)))

  def __add__(self, other):
    assert(self.ib == other.ib and
           self.fb == other.fb and
           self.rnd == other.rnd)
    name = gensym()
    a = zeroext(self.name, 1)
    b = zeroext(other.name, 1)
    res = extract(self.size - 1, 0, clamp(bvadd(a, b), self.size+1))
    fp.__vars.append(decl(name, bv(self.size)))
    fp.__vars.append(equals(name, res))
    return fp(name, self.ib, self.fb, other.rnd, False)

  def __sub__(self, other):
    assert(self.ib == other.ib and
           self.fb == other.fb and
           self.rnd == other.rnd)
    name = gensym()
    a = zeroext(self.name, 1)
    b = zeroext(other.name, 1)
    res = extract(self.size - 1, 0, clamp(bvsub(a, b), self.size+1))
    fp.__vars.append(decl(name, bv(self.size)))
    fp.__vars.append(equals(name, res))
    return fp(name, self.ib, self.fb, other.rnd, False)

  def __mul__(self, other):
    assert(self.ib == other.ib and
           self.fb == other.fb and
           self.rnd == other.rnd)
    name = gensym()
    w = self.size*2
    a = zeroext(self.name, self.size)
    b = zeroext(other.name, self.size)
    c = bvmul(a, b)
    result = extract(w-1, self.size, c)
    fp.__vars.append(decl(name, bv(self.size)))
    fp.__vars.append(equals(name, result))
    return fp(name, self.ib, self.fb, other.rnd, False)
  
  def vars(self):
    return fp.__vars

x = fp('x', 0, 6)
y = fp('y', 0, 6)
z = x + y
w = x*y
a = z+w


print("""(set-logic QF_BV)
(set-option :produce-models true)""")
for v in a.vars():
  print v

print """
(check-sat)
(get-model)
(exit)"""
