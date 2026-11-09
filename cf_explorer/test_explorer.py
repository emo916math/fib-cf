"""Run with: sage -python -m unittest discover -s cf_explorer -v"""
import unittest
import explorer as e
from sage.all import ZZ, lcm, PolynomialRing, matrix, QQ, continued_fraction


def contains(word, part):
    return any(word[j:j+len(part)]==part for j in range(len(word)-len(part)+1))

class ExplorerTests(unittest.TestCase):
    def test_direct(self):
        self.assertEqual(e.power_cf(1,1,5,7),(10,1,3042,2,1,1,2,9))
        self.assertEqual(e.recurrence_pair(1,1,20),(10946,6765))
        with self.assertRaises(ZeroDivisionError): e.power_cf(1,1,1,0)

    def test_determinants(self):
        R=PolynomialRing(ZZ,names=('a','b')); a,b=R.gens()
        for k in range(1,9):
            for i in range(k+1):
                self.assertEqual(e.Delta_polynomial(k,i),e._determinant(k,i,a,b,R))
                self.assertTrue(e.delta_polynomial(k,i).is_monic())
        self.assertEqual(str(e.delta_polynomial(5,2)), 't^3 + 2*t^2 + 3*t - 6')
        for a,b in [(1,1),(2,1),(3,-1),(2,2)]:
            for k in range(1,7):
                for i in range(k+1):
                    if e.Delta(a,b,k,i):
                        self.assertEqual(e.Delta(a,b,k,i)%e.lattice_index(a,b,k,i),0)

    def test_cubic_and_invisible(self):
        self.assertEqual([e.junction(1,1,3,1,n).junction for n in range(3)],
                         [(3,2,3),(1,1,1),(10,)])
        self.assertEqual(e.junction(1,1,3,2),e.PJP((4,),(2,2),(1,)))
        for n in range(10):
            self.assertEqual(e.junction(1,1,4,3,n),e.PJP((11,),(),(11,)))
        self.assertEqual(e.junction(1,1,3,3),e.PJP((1,),(),()))

    def test_moduli(self):
        for a,b in [(1,1),(2,1),(3,-1),(2,2)]:
            for k in range(1,5):
                for i in range(k+1):
                    if not e.Delta(a,b,k,i): continue
                    m=e.junction_modulus(a,b,k,i)
                    d=e.lattice_index(a,b,k,i)
                    if abs(b)==1:
                        self.assertEqual(e.recurrence_pair(a,b,m)[1]%d,0)
                        for j in range(1,m):
                            self.assertNotEqual(e.recurrence_pair(a,b,j)[1]%d,0)
                    elif i:
                        Phi=e._pade_coefficients(a,b,k,i)
                        t=a*a//b
                        N=lcm(QQ(e._minor_denominator(Phi,QQ(a)/b)),
                              QQ(e._minor_denominator(Phi,1/QQ(a)))/t**i)
                        v=lambda j: e.recurrence_pair(a,b,2*j)[1]/(a*QQ(b)**(j-1))
                        self.assertEqual(m%2,0)
                        self.assertEqual(v(m//2)%N,0)
                        for j in range(1,m//2):
                            self.assertNotEqual(v(j)%N,0)

    def test_periodicity(self):
        for a,b,k in [(1,1,3),(1,1,4),(1,1,5),(2,1,3),(3,-1,3),(2,2,3)]:
            for i in range(k+1):
                if not e.Delta(a,b,k,i): continue
                m=e.junction_modulus(a,b,k,i,oriented=True)
                for n in range(min(m,12)):
                    self.assertEqual(e.junction(a,b,k,i,n),e.junction(a,b,k,i,n+m),
                                     (a,b,k,i,n,m))

    def test_monster_parity_and_enumeration(self):
        with self.assertRaises(e.MonsterJunctionError): e.junction(1,1,5,2)
        self.assertEqual(e.junction_modulus(1,1,5,1),5)
        self.assertEqual(e.junction_modulus(1,1,5,1,oriented=True),10)
        self.assertEqual(e.junction(1,1,5,1,0).junction,(10,1,1))
        self.assertEqual(e.junction(1,1,5,1,5).junction,(10,2))
        data=e.all_junctions(1,1,5)
        self.assertNotIn(2,data)
        self.assertEqual(data[1]['modulus'],10)
        self.assertEqual(sorted(sum((list(v) for v in data[1]['classes'].values()),[])),list(range(10)))
        with self.assertRaises(ValueError): e.all_junctions(2,4,5,max_classes=10)
        with self.assertRaises(NotImplementedError): e.junction_modulus(1,3,2,1)

    def test_against_direct_words(self):
        # Independent exact rational CFs; no reuse of the Padé algorithm.
        for a,b,k in [(1,1,3),(1,1,4),(1,1,5),(2,1,3),(3,-1,3),
                      (2,2,3),(3,3,6),(6,6,4),(2,4,5)]:
            monsters=[i for i in range(k+1) if not e.Delta(a,b,k,i)]
            for n in range(200,210):
                word=e.power_cf(a,b,k,n)
                pos=max(range(len(word)),key=word.__getitem__) if monsters else None
                for i in range(k+1):
                    if i in monsters: continue
                    L,J,R=e.junction(a,b,k,i,n)
                    context=(L*2)[-12:]+J+(R*2)[:12]
                    info=(a,b,k,i,n,(L,J,R))
                    if i==0:
                        self.assertEqual(word[:len(context)],context,info)
                    elif i==k:
                        # At a finite terminal cusp either positive expansion is allowed.
                        self.assertTrue(any(W[-len(context):]==context if context else True
                                            for W in (word,e._alternate(word))),info)
                    elif i+1 in monsters:
                        self.assertEqual(word[pos-len(context):pos],context,info)
                    elif i-1 in monsters:
                        self.assertEqual(word[pos+1:pos+1+len(context)],context,info)
                    else:
                        self.assertTrue(contains(word,context),info)

if __name__=='__main__': unittest.main()
