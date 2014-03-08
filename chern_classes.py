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


def reduce_varible_decomposition(n,var_decomp):
    #Takes a symmetric decomposotion with an extra variable and converts it into a decomposition in a
    # new set of variables. In particular given a decomposition of q(t,x_1,x_2,..,x_n) of the form
    # sum(t^i * d_i(x_1,...,x_n) and returns a decomposition of q in t,x_1 ... x_n
    pass


def linear_variable_elementary_extention(n,i):
    # returns a decomposition of the elementary symmetric polynomial e_i(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))
    pass


def linear_variable_decomosition_extention(n,decomp):
    #Takes a symmetric decomposition in of a polynomial q n variable x_1, .., ,x_n and
    # returns a decomposition of the polynomial q(t+x_1,...,t+x_n) as a polynomial in t
    # in particular it returns sum(t^i * d_i(x_1,...,x_n))
    pass


def decompose_combination_polynomial(n,p):
    #Decomoses the combination polynomial. This polynomial has roots x_{i_1}+ ..+x_{i_p} for some combination
    # 1<=i_1<..<i_p<=n
    pass


def decomp_one_combination_polynomial_recursive(n,p):
    #Compute a decomposition of the one combination polynomial by finding a decomposition
    # of the associated composition polynomial doing a linear variable extension and setting
    # the new variable equal to 1.
    #This has the advantage of being able to use a more efficient recursive algorithm to compute
    # a decomposition of the combination polynomial.
    comb_decomp = decompose_combination_polynomial(n,p)
    var_comb_decomp = linear_variable_decomosition_extention(n,comb_decomp)
    #Set the new variable equal to one
    new_var = var_comb_decomp.gens()[0]
    one = var_comb_decomp.parent().one()
    decomp = var_comb_decomp.substitute({new_var : one})
    return decomp

def decomp_one_combination_polynomial(n,p):
    #Current version do naive way.
    return decomp_one_combination_polynomial_recursive(n,p)

if __name__=="__main__":
    print(exterior_power(4,2)) #Basic check