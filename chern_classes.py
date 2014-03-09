from sage.all import *


def prod(list,initial):
    #Forms the product of all elements of the list uses initial as the initial value
    result = initial
    for element in list:
        result *= element
    return result

#File to help compute chern classes and relations between that come up in my academic work


def exterior_power(n,p):
    #Returns the chern class of the pth exterior power of an n dimensional bundle E
    # in terms of the chern class of E

    #Polynomial ring of polynomials in the chern classes.
    chern_ring = PolynomialRing(RationalField(),'c',n+1) # N+1 gens as c_0 is 1 to get the dimensions to agree.
    #By the splitting principle this is the same as computing a decomposition into elementary
    # symmetric polynomials of the polynomial which is the product of
    # (1+x_{i_1}+...x_{i_p}) for each combination of 1<=i_1<..<i_p<=n.
    # We call such a polynomial a one combination polynomial in p and n.
    decomp = decomp_one_combination_polynomial(n,p)
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


def decomp_one_combination_polynomial_naive(n,p):
    #Compute elementary symmetric decomposition the naive way compute the polynomial explicitly and decompose it
    # Using the inbuilt symmetric functions methods
    poly_ring = PolynomialRing(RationalField(),'x',n) # A ring with enough generators to work in.
    #Construct polynomial
    roots = [1+sum(c) for c in Combinations(poly_ring.gens(),p)]
    poly = prod(roots,poly_ring.one())
    #Get elementary symmetric decomposition
    elementary = SymmetricFunctions(RationalField()).elementary()
    return elementary.from_polynomial(poly)


def degree_shift(decomp,degree):
    #Shift all elementary polynomials in decomposition by given degree
    shifted_decomp = decomp.parent().zero()
    for support in decomp.support():
        coefficient = decomp.coefficient(support)
        shifted_support = support[degree:]
        monomial = decomp.parent()[shifted_support]
        shifted_decomp += coefficient * monomial
    return shifted_decomp


def variable_unique_expansion_elementary(n,i,poly_ring):
    #Given an elementary symmetric polynomial in n variables gives the unique polynomial in a new variable t
    # such that the constant part is the ith symmetric polynomial and the polynomial is symmetric in the
    # variables t,x1,..,xn
    t = poly_ring.gens()[0]
    e = poly_ring.base_ring()
    return e[i] + t*e[i-1]


def variable_unique_expansion_decomposition(n,decomp,poly_ring):
    #Given an elementary symmetric polynomial decomposition in n variables gives the shifted by degree
    # unique polynomial in a new variable t such that the constant part is the given decomposition
    # and the polynomial is a symmetric decomposition in the variables t,x1,..,xn
    expansion = poly_ring.zero()
    for support in decomp.support():
        coefficient = decomp.coefficient(support)
        monomial = poly_ring.one()
        for el in support:
            monomial *= variable_unique_expansion_elementary(n, el, poly_ring)
        expansion += coefficient*monomial
    return expansion


def reduce_variable_decomposition(n,var_decomp):
    #Takes a symmetric decomposotion with an extra variable and converts it into a decomposition in a
    # new set of variables. In particular given a decomposition of q(t,x_1,x_2,..,x_n) of the form
    # sum(t^i * d_i(x_1,...,x_n) and returns a decomposition of q in t,x_1 ... x_n

    #Use the relation that e_i(x_1,...,x_n) = t.e_{i-1}(x_1...x_{n-1}) + e_i(x_1,..,x_{n-1})
    # under the relation t -> x_n
    #New polynmial ring to work in

    #From lowest degree of variable t to the highest reduce decomp by the unique expansion of this coeffieicent
    var_poly_ring = var_decomp.parent()
    t = var_poly_ring.gens()[0]
    elementary = var_poly_ring.base_ring()
    degree = 0  # current lowest degree
    reduced_decomp = elementary.zero() # current reduced decomposition
    while not var_decomp.is_zero():
        coefficient = var_decomp[degree]
        shifted_coefficient = degree_shift(coefficient,degree)
        unique_expand = variable_unique_expansion_decomposition(n,shifted_coefficient,var_poly_ring)
        #Reduce the variable decomposition by the expansion shifted to the required degree
        # add this level to th reduced decomposition shifted to the required degree
        var_decomp -= unique_expand*(t**degree)*(elementary[n-1]**degree)
        reduced_decomp += shifted_coefficient*(elementary[n]**degree)
        #Increase degree for next iteration
        degree += 1
    return reduced_decomp

_elementary_linear_extension_cache = {}


def linear_variable_elementary_extension(n,i):
    # returns a decomposition of the elementary symmetric polynomial e_i(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))
    #Use cache to save time as may be called often with same arguments
    if (n,i) in _elementary_linear_extension_cache:
        return _elementary_linear_extension_cache[(n,i)]
    #Construct the polynomial ring in a single variable t over the elementary symmetric algebra
    elementary = SymmetricFunctions(RationalField()).elementary()
    poly_ring = PolynomialRing(elementary,'t')
    t = poly_ring.gens()[0]
    #constuct as a sum of monomials in t
    extension = poly_ring.zero()
    mon_number = binomial(n, i) # number of monomials in e_i
    for j in xrange(i+1):
        monomial = (t**j) * elementary[i-j]
        #Number of monomials times number created at grade j / number in each e_j
        coefficient = (mon_number*binomial(i, j))/binomial(n, j)
        extension += coefficient*monomial
    #Write to cache and return
    _elementary_linear_extension_cache[(n,i)] = extension
    return extension


def linear_variable_decomposition_extension(n, decomp):
    #Takes a symmetric decomposition in of a polynomial q n variable x_1, .., ,x_n and
    # returns a decomposition of the polynomial q(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))

    #Construct the polynomial ring in a single variable t over the elementary symmetric algebra
    elementary = SymmetricFunctions(RationalField()).elementary()
    poly_ring = PolynomialRing(elementary, 't')
    #Ideally here we would use a hom but it is not well supported so fold over the monomials in decomp
    extension = poly_ring.zero()
    for support in decomp.support():
        monomial = poly_ring.one()
        for index in support:
            monomial *= linear_variable_elementary_extension(n,index)
        coefficient = decomp.coefficient(support)
        extension += coefficient * monomial
    return extension


_combination_polynomial_cache = {}

def decompose_combination_polynomial(n,p):
    #Decomoses the combination polynomial. This polynomial has roots x_{i_1}+ ..+x_{i_p} for some combination
    # 1<=i_1<..<i_p<=n
    #We perform this computation recursively based on the following note the combination polynomial of order p
    # q_p(x_1,...,x_n) can be split into the product of q_p(x_1,...,x_{n-1}) and the linear extension with the variable
    # x_n of the polynomial q_{p-1}(x_1,...,x_{n-1})
    #As this algorithm is recursive we cache results to improve efficiency
    if (n,p) in _combination_polynomial_cache:
        return _combination_polynomial_cache[(n,p)]
    #If p=0,1,n then we know the decomposition and just return that
    if p==0:
        #In the case that p==0 return the empty decomposition
        return SymmetricFunctions(RationalField()).elementary()[0]
    if p==1:
        #In the case that p==1 the decomposition is just e_n
        return SymmetricFunctions(RationalField()).elementary()[n]
    if p==n:
        #In the case that p==n the decomposition is just e_1
        return SymmetricFunctions(RationalField()).elementary()[1]
    #Compute the decomposition of the 2 parts corresponding to the roots containing x_n and those not.
    tail_roots = decompose_combination_polynomial(n-1,p)
    initial_part = decompose_combination_polynomial(n-1,p-1)
    initial_roots = linear_variable_decomposition_extension(n-1,initial_part)
    #Recombine to get the decomposition of q_n
    #Coerce initial_roots and tail roots into the same ring and multiply
    one = initial_roots.parent().one()
    full_decomp = initial_roots * (one * tail_roots)
    #Recobine to remove extra variable
    decomp = reduce_variable_decomposition(n,full_decomp)
    #Add decomp to cache
    _combination_polynomial_cache[(n,p)] = decomp
    return decomp


def decomp_one_combination_polynomial_recursive(n,p):
    #Compute a decomposition of the one combination polynomial by finding a decomposition
    # of the associated composition polynomial doing a linear variable extension and setting
    # the new variable equal to 1.
    #This has the advantage of being able to use a more efficient recursive algorithm to compute
    # a decomposition of the combination polynomial.
    comb_decomp = decompose_combination_polynomial(n,p)
    var_comb_decomp = linear_variable_decomposition_extension(n,comb_decomp)
    #Set the new variable equal to one
    new_var = var_comb_decomp.parent().gens()[0]
    one = var_comb_decomp.parent().one()
    decomp = var_comb_decomp.substitute({new_var : one})
    #Need to coerce decomp back into the elementary ring
    decomp = decomp.constant_coefficient()
    return decomp

def decomp_one_combination_polynomial(n,p):
    #Current version do naive way.
    return decomp_one_combination_polynomial_recursive(n,p)

#if __name__=="__main__":
#    print(exterior_power(4,2)) #Basic check