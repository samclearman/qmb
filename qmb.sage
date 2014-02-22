import re
#
# Helper functions
#

def gen_names(n):
    return ['r' + str(i) + 'c' + str(j) for i in [1..n] for j in [1..n]]

def long_element_list(mon):
    l = []
    for t in mon._element_list:
        l += [t[0]] * t[1]
    return l

def slc(mon,i,j):
    if j == "end": j = len(long_element_list(mon)) 
    return mon.parent()(zip(long_element_list(mon)[i:j], [1] * (j-i)))

def srch(mon, query):
    m_list = long_element_list(mon)
    q_list = long_element_list(query)
    q_len = len(q_list)
    for i in range(len(m_list) - q_len + 1):
        if m_list[i: i + q_len] == q_list:
            return i
    return -1

def subs(mon, old, new):
    i =  srch(mon, old)
    if i > -1:
        l = len(long_element_list(old))
        return slc(mon, 0,i) * new * slc(mon, i+l, "end")
    raise NotFoundError("Relation cannot be applied")

def to_mon(elm):
    l = list(elm)
    if len(l) > 1 or l[0][0] != 1:
        raise TypeError("Can't convert to monoid element: must be a single monomial with coefficient 1")
    else:
        return l[0][1]

def algebra_element_from_list(algebra, list):
    elm = algebra(0)
    for t in list:
        elm = elm + t[0] * algebra(t[1])
    return elm

def replace_monomial(element, i, replacement):
    l = list(element)
    return (l[0][0] * replacement) + element.parent()(l[1:])

def monomial_to_words(mon):
    rows, cols = [],[]
    rownum = re.compile("r([0-9]+)")
    colnum = re.compile("c([0-9]+)")
    for name in mon.to_word():
        rows.append(Integer(rownum.findall(name)[0]))
        cols.append(Integer(colnum.findall(name)[0]))
    return Word(rows),Word(cols)

def evaluate_monomial(mon, A):
    result = 1
    (rows,cols) = monomial_to_words(mon)
    for (i,j) in zip(rows, cols):
        result *= A[i - 1][j - 1]
    return result

class NotFoundError(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)


from sage.algebras.free_algebra_element import FreeAlgebraElement

class QuantumMatrixBialgebraElement(FreeAlgebraElement):

    def __init__(self, A, x):
        FreeAlgebraElement.__init__(self, A, x)
    
    def display(self):
        rep = FreeAlgebraElement.__repr__(self)
        rep = rep.replace("r","%s_"%(self.parent().prefix))
        rep = rep.replace("c", ",")
        # tex = re.sub("r([0-9]+?)c([0-9]+?)", "x_{\1,\2}", tex)
        return rep
    
    def canonical(self):
        if self == 0:
            return self
        rels = self.parent().relations()
        elist = list(self)
        # Basically all this is doing is just trying each relation.
        # The recursion is window dressing that should very slightly improve
        # efficiency.
        for k in rels:
            mon = to_mon(k)
            try:
                replacement = subs(elist[0][1], mon, rels[k])
                return replace_monomial(self, 0, replacement).canonical()
            except NotFoundError:
                pass
        return self.parent()(elist[:1]) + self.parent()(elist[1:]).canonical()
    
    def sigma(self, A):
        result = 0
        for t in self:
            w = monomial_to_words(t[1])[1]
            q_ew = self.parent().variable**(len(w.inversions())/2)
            result += t[0] * q_ew * evaluate_monomial(t[1], A)
        return result


from sage.algebras.free_algebra import FreeAlgebra_generic
            
class QuantumMatrixBialgebra(FreeAlgebra_generic):
    
    Element = QuantumMatrixBialgebraElement
    
    def __init__(self, variable, m,n=None, prefix="x"):
        if not n: n = m
        self.height = m
        self.width = n
        self.variable = variable
        self.prefix = prefix
        # Should check to make sure that variable is a member of an appropriate ring
        FreeAlgebra_generic.__init__(self, variable.parent(), n * m, ['r' + str(i) + 'c' + str(j) for i in range(1,m+1) for j in range(1,n+1)])
    
    def F(self):
        q = self.variable
        return q**(1/2) - q**(-1/2)
        
    def _element_constructor_(self, x):
        # Attempt to treat as a list of tuples
        try:
            elm = FreeAlgebra_generic._element_constructor_(self, 0)
            if not isinstance(x, list) : raise TypeError
            for t in x:
                if len(t) != 2: raise TypeError
                elm = elm + (t[0] * FreeAlgebra_generic._element_constructor_(self, t[1]))
            return elm
        except (TypeError, IndexError):
            # workaround for a bug in FreeAlgebra
            try:
                _ = CC(x)
                x = self.base_ring()(x)
                return self(x)
            except:
                return FreeAlgebra_generic._element_constructor_(self, x)
    
    def __repr__(self):
        return "%d by %d Quantum Matrix Bialgebra"%(self.width, self.height)
    
    def gen(self, i, j=None):
        if not j:
            return FreeAlgebra_generic.gen(self, i)
        return self("r%dc%d"%(i,j))
    
    @cached_method
    def relations(self):
        m = self.height
        n = self.width
        x = self.gen
        rels = {}
        for i in range(1,m+1):
            for k in range(1,n+1):
                for l in range(k+1,n+1):
                    rels[x(i,l) * x(i,k)] = self.variable * x(i,k) * x(i,l)
        for k in range(1,n+1):
            for i in range(1,m+1):
                for j in range(i+1,m+1):
                    rels[x(j,k) * x(i,k)] = self.variable * x(k,i) * x(l,i)
        for i in range(1,n+1):
            for j in range(i+1,n+1):
                for k in range(1,m+1):
                    for l in range(k+1,m+1):
                        rels[x(j,k) * x(i,l)] = x(i,l) * x(j,k)
                        rels[x(j,l) * x(i,k)] = x(i,k) * x(j,l) + (self.F() * x(i,l) * x(j,k))
        return rels

def quantumdeterminant(AA, I, J):
    q = AA.variable
    x = AA.gen
    det = AA(0)
    for pi in Permutations(len(J)):
        Jshuffled = pi.action(J)
        mon = AA((-((q)**(-1/2)))**(len(pi.inversions())))
        for i in range(len(I)):
            mon *= x(I[i], Jshuffled[i])
        det += mon
    return det

def quantumpermanant(AA, I, J):
    q = AA.variable
    x = AA.gen
    per = AA(0)
    for pi in Permutations(len(J)):
        Jshuffled = pi.action(J)
        mon = AA(((q)**(1/2))**(len(pi.inversions())))
        for i in range(len(I)):
            mon *= x(I[i], Jshuffled[i])
        per += mon
    return per