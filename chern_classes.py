from sage.all import *


def prod(list, initial):
    #Forms the product of all elements of the list uses initial as the initial value
    result = initial
    for element in list:
        result *= element
    return result

#File to help compute chern classes and relations between that come up in my academic work


class VectorBundle:
    #Class to group together chern classes of a bundle.
    # This means that gradings can be preserved better.
    def __init__(self, name, dim, chern_classes=None, truncate=None):
        #Create a bundle with a given name
        # Either give the dimension or a list of chern clases.
        # In the case of a dimension the chern classes will be abstractly set to names of the form c_i(name)
        # In the case of a list of chern classes they will be coerced into the same ring.
        #Optional parameter to truncate and only use the first truncate chern classes.

        self.name = name
        self.dim = dim
        #Set the truncation degree if given in this case the dim must be given
        if truncate:
            self.truncated = True
            self.truncation = truncate
        else:
            self.truncated = False
            self.truncation = dim

        if chern_classes:
            #Get the variables used in all the chern classes to construct a ring containing the all
            variables = set([])
            for chern_class in chern_classes:
                variables.update(chern_class.parent().variable_names_recursive())
            self.chern_ring = PolynomialRing(QQ,list(variables))
            #Multiply each chern class by 1 in the chern ring to coerce.
            self.chern_classes = [self.chern_ring.one()]
            for i in xrange(self.truncation):
                self.chern_classes.append(self.chern_ring.one() * chern_classes[i+1])
        else:
            #If the chern classes are not set construct names for each of them and make the ring based on this
            self.dim = dim
            variables = ["c_"+str(i+1)+"("+name+")" for i in xrange(dim)]
            self.chern_ring = PolynomialRing(QQ,variables)
            self.chern_classes = [self.chern_ring.one()]
            #Set the chern classes to there appropriate generator.
            for i in xrange(self.truncation):
                self.chern_classes.append(self.chern_ring.gens(i))

    def total_chern_class(self):
        #Returns the total chern class given as the sum of
        return sum(self.chern_classes)

    def twist(self, line_bundle, name=None):
        #Returns the Vector bundle with is the tensor product of this bundle and a complex line
        # Also give a new optional name else ne will be constructed
        if not line_bundle.dim == 1:
            #Other bundle must be a lne bundle
            return ValueError
        #Create new chern ring with all classes exist in
        new_chern_ring = PolynomialRing(QQ, self.chern_ring.variable_names() + line_bundle.variable_names())
        #Get first chern class of line bundle coerced
        c1 = line_bundle.chern_classes[1] * new_chern_ring.one()
        #Compute new chern classes using binomial formula
        # -- see notes for sum formula.
        new_chern_classes = []
        for i in xrange(self.truncation):
            new_chern_class_i = new_chern_ring.zero()
            for j in xrange(i):
                new_chern_class_i += binomial(self.dim-j,i-j) * c1**(i-j) * self.chern_classes[j]
            new_chern_classes.append(new_chern_class_i)

        if not name:
            #Use * to indicate tensor product if new name not given
            name = self.name + '*' + line_bundle.name
        if self.truncated:
            return VectorBundle(name, self.dim, new_chern_classes, self.truncation)
        else:
            return VectorBundle(name, self.dim, new_chern_classes)

    def sum(self, bundle, name=None):
        #Returns the Vector bundle which is the sum of this bundle and the given bundle.
        # Also give a new optional name else one will be constructed.
        if not name:
            #Use + to indicate direct sum if new name not given
            name = self.name + '+' + bundle.name
        #Create new chern ring which all classes exist in
        new_chern_ring = PolynomialRing(QQ, self.chern_ring.variable_names() + bundle.variable_names())
        #Compute new chern classes using whitney formula
        new_chern_classes = []
        #If this or the other bundle is truncated only truncate the resultant bundle to the minimum of these 2
        if self.truncated or bundle.truncated:
            max_degree = min(self.truncation, bundle.truncation)
        else:
            max_degree = self.dim + bundle.dim
        for i in xrange(max_degree):
            new_chern_class_i = new_chern_ring.zero()
            for j in xrange(i):
                #Check that both indices are within bounds else the product is zero.
                #Coerse with new chern ring
                if j < self.truncation and i-j < bundle.truncation:
                    new_chern_class_i += (new_chern_ring.one() * self.chern_classes[j]) * bundle.chern_classes[i-j]
            new_chern_classes.append(new_chern_class_i)
        #Return new bundle - with correct truncation
        if self.truncated or bundle.truncated:
            return VectorBundle(name, self.dim+bundle.dim, new_chern_classes, max_degree)
        else:
            return VectorBundle(name, self.dim+bundle.dim, new_chern_classes)

    def multiple(self, n, name=None):
        #Returns a Vector bundle with is the direct sum of this bundle n times
        # Also give a new optional name else one will be constructed.
        if n < 1:
            #Thi method cannot handle inverses or zero multiples.
            raise ValueError
        if not name:
            #Use append number to front to indicate multiple by n.
            name = str(n) + self.name
        #Repeatly use the sum formula accumulating in this copy of self
        acc = VectorBundle(name, chern_classes=list(self.chern_classes))
        for _ in xrange(n-1):
            acc = acc.sum(self, name)
        return acc


class LineBundle(VectorBundle):
    #Specialisation of Vector bundle to line bundles - this allows and inverse to be computed.

    def __init__(self, name, chern_class=None):
        #Creates a ine bundle with the given name unless a chern class is given the first chern class
        # of this bundle is the same as the name
        if chern_class:
            chern_classes = [chern_class.parent().one(), chern_class]
        else:
            chern_classes = [PolynomialRing(QQ, name).one(), self.chern_ring.gen()]
        VectorBundle.__init__(self, name, chern_classes=chern_classes)

    def inverse(self, name=None):
        #Returns the inverse of this line bundle
        #Takes an optional name to call this bundle else it will be called name_inv
        if not name:
            name = self.name+"_inv"
        return LineBundle(name, -self.chern_classes[1])

    def power(self, n, name=None):
        #Returns this bundle (or it's inverse) tensored wih itself n times
        #Takes an optional name parameter
        #In the case that n == -1 this is the same as inverse.
        if not name:
            if n > 0:
                name = self.name+'_' + str(n)
            elif n < 0:
                name = self.name+'_inv_' + str(n)
            else:
                name = '1'  # The trivial bundle
        return LineBundle(name, n*self.chern_classes[1])

def exterior_power(n, p, algorithm="recursive",degree=None):
    #Returns the chern class of the pth exterior power of an n dimensional bundle E
    # in terms of the chern class of E
    #Optional algorithm property gives the algorithm used to decompose polynomial of line bundles
    # Naive corresponds to computing the full polynomial mostly used for testing
    #If positive degree is given just return the chern class less than that degree.

    #Polynomial ring of polynomials in the chern classes.
    # N+1 gens as c_0 is 1 to get the dimensions to agree.
    # deglex is used to quickly see the equal degree parts.
    chern_ring = PolynomialRing(RationalField(), 'c', n+1, order='deglex')
    #By the splitting principle this is the same as computing a decomposition into elementary
    # symmetric polynomials of the polynomial which is the product of
    # (1+x_{i_1}+...x_{i_p}) for each combination of 1<=i_1<..<i_p<=n.
    # We call such a polynomial a one combination polynomial in p and n.
    decomp = _decompose_one_combination_polynomial(n, p, algorithm,degree)
    #Convert the decomposition into a polynomial in the chern classes.
    chern = chern_ring.zero()
    chern_gens = chern_ring.gens()
    monomial_coefficients = decomp.monomial_coefficients()
    #Directly convert elementary symmetric monomials to monomials in chern generators
    # Would like to do this with a hom
    for monomial in monomial_coefficients:
        coefficient = monomial_coefficients[monomial]
        #As all chern classes of E are zero in degree greater than n
        # only include those monomials containing elementary symmetric polynomials
        # with degree less than or equal to n.
        if all(degree <= n for degree in monomial):
            chern += coefficient*prod([chern_gens[i] for i in monomial], chern_ring.one())
    return chern

def _clean_higher_terms(decomp, n):
    #Removes all the terms in decomposition with a support containing e_i with i>n
    # if computing over n variables then such a e_i must be zero
    cleaned_decomp = decomp.parent().zero()
    for support in decomp.support():
        if len(support) == 0 or max(support) <= n:
            cleaned_decomp += decomp.coefficient(support) * decomp.parent()[support]
    return cleaned_decomp


def _filter_by_degree(decomp, degree):
    #Returns the homogeneous part of the decomposition less than the given positive degree where the degree of e_i is i
    filtered_decomp = decomp.parent().zero()
    for support in decomp.support():
        if sum(support) < degree:
            filtered_decomp += decomp.coefficient(support) * decomp.parent()[support]
    return filtered_decomp


def _filter_by_var_degree(var_decomp, degree):
    #Returns the homogeneous part of a polynomial decomposition less than the given positive degree
    # where the degree of e_i is i and the degree of t is 1
    poly_ring = var_decomp.parent()
    t = poly_ring.gens()[0]
    filtered_decomp = poly_ring.zero()
    for i in xrange(var_decomp.degree()+1):
        if degree <= i:
            break
        filtered_decomp += t**i * _filter_by_degree(var_decomp[i], degree-i)
    return filtered_decomp


def _decomp_one_combination_polynomial_naive(n, p, degree):
    #Compute elementary symmetric decomposition the naive way compute the polynomial explicitly and decompose it
    # Using the inbuilt symmetric functions methods
    poly_ring = PolynomialRing(RationalField(), 'x', n) # A ring with enough generators to work in.
    #Construct polynomial
    roots = [1+sum(c) for c in Combinations(poly_ring.gens(), p)]
    poly = prod(roots,poly_ring.one())
    #Get elementary symmetric decomposition
    elementary = SymmetricFunctions(RationalField()).elementary()
    decomp = _clean_higher_terms(elementary.from_polynomial(poly), n)
    if degree:
        #If degree is present filter the decomposition to just return that component
        decomp = _filter_by_degree(decomp, degree)
    return decomp


def _degree_shift(decomp, degree):
    #Shift all elementary polynomials in decomposition by given degree
    shifted_decomp = decomp.parent().zero()
    for support in decomp.support():
        coefficient = decomp.coefficient(support)
        shifted_support = support[degree:]
        monomial = decomp.parent()[shifted_support]
        shifted_decomp += coefficient * monomial
    return shifted_decomp


def _variable_unique_expansion_elementary(n, i, poly_ring):
    #Given an elementary symmetric polynomial in n variables gives the unique polynomial in a new variable t
    # such that the constant part is the ith symmetric polynomial and the polynomial is symmetric in the
    # variables t,x1,..,xn
    t = poly_ring.gens()[0]
    e = poly_ring.base_ring()
    return e[i] + t*e[i-1]


def _variable_unique_expansion_decomposition(n, decomp, poly_ring):
    #Given an elementary symmetric polynomial decomposition in n variables gives the shifted by degree
    # unique polynomial in a new variable t such that the constant part is the given decomposition
    # and the polynomial is a symmetric decomposition in the variables t,x1,..,xn
    expansion = poly_ring.zero()
    for support in decomp.support():
        coefficient = decomp.coefficient(support)
        monomial = poly_ring.one()
        for el in support:
            monomial *= _variable_unique_expansion_elementary(n, el, poly_ring)
        expansion += coefficient*monomial
    return expansion


def _reduce_variable_decomposition(n, var_decomp):
    #Takes a symmetric decomposition with an extra variable and converts it into a decomposition in a
    # new set of variables. In particular given a decomposition of q(t,x_1,x_2,..,x_n) of the form
    # sum(t^i * d_i(x_1,...,x_n) and returns a decomposition of q in t,x_1 ... x_n

    #Use the relation that e_i(x_1,...,x_n) = t.e_{i-1}(x_1...x_{n-1}) + e_i(x_1,..,x_{n-1})
    # under the relation t -> x_n
    #New polynomial ring to work in

    #From lowest degree of variable t to the highest reduce decomposition by the unique expansion of this coefficient
    var_poly_ring = var_decomp.parent()
    t = var_poly_ring.gens()[0]
    elementary = var_poly_ring.base_ring()
    degree = 0  # current lowest degree
    reduced_decomp = elementary.zero() # current reduced decomposition
    while not var_decomp.is_zero():
        coefficient = var_decomp[degree]
        shifted_coefficient = _degree_shift(coefficient, degree)
        unique_expand = _variable_unique_expansion_decomposition(n, shifted_coefficient, var_poly_ring)
        #Reduce the variable decomposition by the expansion shifted to the required degree
        # add this level to th reduced decomposition shifted to the required degree
        var_decomp -= unique_expand*(t**degree)*(elementary[n-1]**degree)
        reduced_decomp += shifted_coefficient*(elementary[n]**degree)
        #Increase degree for next iteration
        degree += 1
    return _clean_higher_terms(reduced_decomp, n)

_elementary_linear_extension_cache = {}


def _linear_variable_elementary_extension(n,i):
    # returns a decomposition of the elementary symmetric polynomial e_i(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))
    #Use cache to save time as may be called often with same arguments
    if (n,i) in _elementary_linear_extension_cache:
        return _elementary_linear_extension_cache[(n,i)]
    #Construct the polynomial ring in a single variable t over the elementary symmetric algebra
    elementary = SymmetricFunctions(RationalField()).elementary()
    poly_ring = PolynomialRing(elementary, 't')
    t = poly_ring.gens()[0]
    #constuct as a sum of monomials in t
    extension = poly_ring.zero()
    mon_number = binomial(n, i) # number of monomials in e_i
    for j in xrange(i+1):
        monomial = (t**j) * elementary[i-j]
        #Number of monomials look at number of monomials x_1 ... x_{i-j}
        # number of x_1 ... x_{i-j} in expansion of a monomial of e_i
        # * number of monomials in e_i containing x_1...x_{i-j}
        coefficient = binomial(n-i+j, j)
        extension += coefficient*monomial
    #Write to cache and return
    cleaned_extension = extension.map_coefficients(lambda x:_clean_higher_terms(x, n))
    _elementary_linear_extension_cache[(n, i)] = cleaned_extension
    return cleaned_extension


def _linear_variable_decomposition_extension(n, decomp):
    #Takes a symmetric decomposition in of a polynomial q n variable x_1, .., ,x_n and
    # returns a decomposition of the polynomial q(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))

    #Construct the polynomial ring in a single variable t over the elementary symmetric algebra
    elementary = SymmetricFunctions(RationalField()).elementary()
    poly_ring = PolynomialRing(elementary, 't')
    #Ideally here we would use a hom but it is not well supported so fold over the monomials in decomposition
    extension = poly_ring.zero()
    for support in decomp.support():
        monomial = poly_ring.one()
        for index in support:
            monomial *= _linear_variable_elementary_extension(n, index)
        coefficient = decomp.coefficient(support)
        extension += coefficient * monomial
    cleaned_extension = extension.map_coefficients(lambda x:_clean_higher_terms(x, n))
    return cleaned_extension


#Cache of previous smaller results to improve recursion
_combination_polynomial_cache = {}

def _decompose_one_combination_polynomial_recursive(n, p, degree):
    #We perform this computation recursively based on the following note the combination polynomial of order p
    # q_p(x_1,...,x_n) can be split into the product of q_p(x_1,...,x_{n-1}) and the linear extension with the variable
    # x_n of the polynomial q_{p-1}(x_1,...,x_{n-1})

    #See if required data is in the cache
    if (n, p, degree) in _combination_polynomial_cache:
        return _combination_polynomial_cache[(n, p, degree)]
    #Elementary symmetric function algebra
    elementary = SymmetricFunctions(RationalField()).elementary()
    #Give results for base cases
    if p > n:
        #If p > n then the polynomial is trivial
        return _filter_by_degree(elementary.zero())
    if p == 0:
        #If p==0 then the polynomial == 1
        return _filter_by_degree(elementary[[]])
    if p == 1:
        #If p==1 then this is the defining polynomial of the elementary symmetric polynomials
        #If degree is specified only return part with needed degree
        elem_sum = [elementary[i] for i in xrange(n+1)]
        return _filter_by_degree(sum(elem_sum), degree)
    if p == n:
        #If p==n then only one combination is possible and q_n = 1+e_1
        return _filter_by_degree(elementary[[0]]+elementary[[1]], degree)
    #Else recurse and get the decompositions of initial and tail roots
    #Get the full decomposition for now in the head and tail.
    tail_roots = _decompose_one_combination_polynomial_recursive(n-1, p, degree)
    initial_part = _decompose_one_combination_polynomial_recursive(n-1, p-1, degree)
    initial_roots = _linear_variable_decomposition_extension(n-1, initial_part)
    #Renormalize as the extra variable is split between p-1 variables
    normalized_roots = initial_roots.parent().zero()
    t = initial_roots.parent().gens()[0]
    for i in xrange(initial_roots.degree()+1):
        coefficient = initial_roots[i]
        exponent = t * (1/(p-1)*elementary[[]])
        normalized_roots += coefficient*(exponent**i)
    #Remove higher unneeded parts from the decomposition
    normalized_roots = _filter_by_var_degree(normalized_roots, degree)
    #Recombine to get a decomposition of q_n
    full_decomp = normalized_roots * tail_roots
    #Remove extra variable to get a decomposition n terms of x_1,..,x_n
    #filter to roots by degree as the reduce functions preserves degree
    full_decomp = _filter_by_var_degree(full_decomp, degree)
    decomp = _reduce_variable_decomposition(n, full_decomp)
    #Reduce degree - should be redundant!
    decomp = _filter_by_degree(decomp, degree)
    #Add to cache and return
    _combination_polynomial_cache[(n, p, degree)] = decomp
    return decomp


def _decompose_one_combination_polynomial(n, p, algorithm="recursive", degree=None):
    #Optional algorithm property gives the algorithm used to decompose polynomial of line bundles
    # Naive corresponds to computing the full polynomial mostly used for testing
    #If positive degree is given only return the part of the decomposition less than that degree.

    #Default to a degree which returns everything.
    if not degree:
        degree = binomial(n, p)+1
    if algorithm=="naive":
        return _decomp_one_combination_polynomial_naive(n, p, degree)
    #Default to using recursive algorithm
    return _decompose_one_combination_polynomial_recursive(n, p, degree)

#if __name__=="__main__":
    #print(exterior_power(4,2)) #Basic check