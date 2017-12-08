# MIT 6.034 Lab 4: Constraint Satisfaction Problems
# Written by Dylan Holmes (dxh), Jessica Noss (jmn), and 6.034 staff

from constraint_api import *
from test_problems import get_pokemon_problem

#### PART 1: WRITE A DEPTH-FIRST SEARCH CONSTRAINT SOLVER

def has_empty_domains(csp) :
    "Returns True if the problem has one or more empty domains, otherwise False"
    for variable in csp.domains:
        # if not value associated with a variable return True
        if len(csp.domains[variable]) == 0:
            return True
    return False

def check_all_constraints(csp) :
    """Return False if the problem's assigned values violate some constraint,
    otherwise True"""
    assigned_vars = csp.assigned_values

    # check every variable against every other variable
    for var1 in assigned_vars:
        for var2 in assigned_vars:
            for constraint in csp.constraints_between(var1,var2):
                # if the constraint fails
                if not constraint.check(assigned_vars[var1],assigned_vars[var2]):
                    return False
    return True
    

def solve_constraint_dfs(problem) :
    """Solves the problem using depth-first search.  Returns a tuple containing:
    1. the solution (a dictionary mapping variables to assigned values), and
    2. the number of extensions made (the number of problems popped off the agenda).
    If no solution was found, return None as the first element of the tuple."""

    agenda = [problem]
    extension_count = 0

    while agenda != []:
        current_problem = agenda.pop(0)
        extension_count +=1
        
        if not has_empty_domains(current_problem) and check_all_constraints(current_problem):
            if current_problem.unassigned_vars == []:
                return (current_problem.assigned_values, extension_count)
            
            unassigned_var = current_problem.pop_next_unassigned_var()
 
            new_problems =  [current_problem.copy().set_assigned_value(unassigned_var,val) for val in current_problem.get_domain(unassigned_var)]

            agenda = new_problems + agenda 

    # completely unsolvable then
    return (None, extension_count)
            

#### PART 2: DOMAIN REDUCTION BEFORE SEARCH

def eliminate_from_neighbors(csp, var) :
    """Eliminates incompatible values from var's neighbors' domains, modifying
    the original csp.  Returns an alphabetically sorted list of the neighboring
    variables whose domains were reduced, with each variable appearing at most
    once.  If no domains were reduced, returns empty list.
    If a domain is reduced to size 0, quits immediately and returns None."""
    
    reduced_domain = set() #use set so we don't have duplicates
    
    var_domain = csp.get_domain(var)

    for neighbor in csp.get_neighbors(var):
        constraint_list = csp.constraints_between(var,neighbor)
        
        for valn in list(csp.get_domain(neighbor)): # wrap in new list so we can modify the original neighbor domain
            valn_invalid = True # assume val2 is invalid, until proven otherwise

            for val in var_domain:

                # apply (val,valn) to all constraints in constraint_list, and filter to keep only ones that failed
                failed_constraints = [constraint for constraint in constraint_list if not constraint.check(val,valn)]

                # if there are no failed constraint, this val2 is compatible with at least one val1.
                if not failed_constraints:
                    valn_invalid = False

            if valn_invalid:
                reduced_domain.add(neighbor)
                csp.eliminate(neighbor,valn)
                if not csp.get_domain(neighbor):
                    return None

    return sorted(list(reduced_domain))



def domain_reduction(csp, queue=None) :
    """Uses constraints to reduce domains, modifying the original csp.
    If queue is None, initializes propagation queue by adding all variables in
    their default order.  Returns a list of all variables that were dequeued,
    in the order they were removed from the queue.  Variables may appear in the
    list multiple times.
    If a domain is reduced to size 0, quits immediately and returns None."""
    if queue == None:
        queue = csp.get_all_variables()
    dequeued_elements = []
    
    while queue != []:
        var = queue.pop(0)
        dequeued_elements.append(var)
        reduced_vars = eliminate_from_neighbors(csp,var)

        if reduced_vars:
            queue.extend([reduced_var for reduced_var in reduced_vars if reduced_var not in queue])
            
        if has_empty_domains(csp):
            return None
        
    return dequeued_elements
    
        
        

# QUESTION 1: How many extensions does it take to solve the Pokemon problem
#    with dfs if you DON'T use domain reduction before solving it?

# Hint: Use get_pokemon_problem() to get a new copy of the Pokemon problem
#    each time you want to solve it with a different search method.

ANSWER_1 = 20

# QUESTION 2: How many extensions does it take to solve the Pokemon problem
#    with dfs if you DO use domain reduction before solving it?

ANSWER_2 = 6


#### PART 3: PROPAGATION THROUGH REDUCED DOMAINS

def solve_constraint_propagate_reduced_domains(problem) :
    """Solves the problem using depth-first search with forward checking and
    propagation through all reduced domains.  Same return type as
    solve_constraint_dfs."""
    agenda = [problem]
    extension_count = 0

    while agenda != []:
        current_problem = agenda.pop(0)
        extension_count +=1
        
        if not has_empty_domains(current_problem) and check_all_constraints(current_problem):
            if current_problem.unassigned_vars == []:
                return (current_problem.assigned_values, extension_count)
            
            unassigned_var = current_problem.pop_next_unassigned_var()
 
            new_problems =  [current_problem.copy().set_assigned_value(unassigned_var,val) for val in current_problem.get_domain(unassigned_var)]
            map(lambda csp: domain_reduction(csp,[unassigned_var]), new_problems)
            
            agenda = new_problems + agenda 

    # completely unsolvable then
    return (None, extension_count)

            
# QUESTION 3: How many extensions does it take to solve the Pokemon problem
#    with propagation through reduced domains? (Don't use domain reduction
#    before solving it.)

ANSWER_3 = 7


#### PART 4: PROPAGATION THROUGH SINGLETON DOMAINS

def domain_reduction_singleton_domains(csp, queue=None) :
    """Uses constraints to reduce domains, modifying the original csp.
    Only propagates through singleton domains.
    Same return type as domain_reduction."""
    if queue == None:
        queue = csp.get_all_variables()
    dequeued_elements = []
    
    while queue != []:
        var = queue.pop(0)
        dequeued_elements.append(var)
        reduced_vars = eliminate_from_neighbors(csp,var)

        if reduced_vars:
            reduced_vars_singleton = [var_s for var_s in reduced_vars if len(csp.get_domain(var_s)) ==1]
            queue.extend(reduced_vars_singleton)
            
        if has_empty_domains(csp):
            return None
        
    return dequeued_elements

def solve_constraint_propagate_singleton_domains(problem) :
    """Solves the problem using depth-first search with forward checking and
    propagation through singleton domains.  Same return type as
    solve_constraint_dfs."""
    agenda = [problem]
    extension_count = 0

    while agenda != []:
        current_problem = agenda.pop(0)
        extension_count +=1
        
        if not has_empty_domains(current_problem) and check_all_constraints(current_problem):
            if current_problem.unassigned_vars == []:
                return (current_problem.assigned_values, extension_count)
            
            unassigned_var = current_problem.pop_next_unassigned_var()
 
            new_problems =  [current_problem.copy().set_assigned_value(unassigned_var,val) for val in current_problem.get_domain(unassigned_var)]
            map(lambda csp: domain_reduction_singleton_domains(csp,[unassigned_var]), new_problems)
            
            agenda = new_problems + agenda 

    # completely unsolvable then
    return (None, extension_count)



# QUESTION 4: How many extensions does it take to solve the Pokemon problem
#    with propagation through singleton domains? (Don't use domain reduction
#    before solving it.)

ANSWER_4 = 8


#### PART 5: FORWARD CHECKING

def propagate(enqueue_condition_fn, csp, queue=None) :
    """Uses constraints to reduce domains, modifying the original csp.
    Uses enqueue_condition_fn to determine whether to enqueue a variable whose
    domain has been reduced.  Same return type as domain_reduction."""
    if queue == None:
        queue = csp.get_all_variables()
    dequeued_elements = []
    
    while queue != []:
        var = queue.pop(0)
        dequeued_elements.append(var)
        reduced_vars = eliminate_from_neighbors(csp,var)

        if reduced_vars:
            reduced_vars_for_queue = [var_s for var_s in reduced_vars if enqueue_condition_fn(csp,var_s)]
            queue.extend(reduced_vars_for_queue)
            
        if has_empty_domains(csp):
            return None
        
    return dequeued_elements

def condition_domain_reduction(csp, var) :
    """Returns True if var should be enqueued under the all-reduced-domains
    condition, otherwise False"""
    return True

def condition_singleton(csp, var) :
    """Returns True if var should be enqueued under the singleton-domains
    condition, otherwise False"""
    return len(csp.get_domain(var)) ==1

def condition_forward_checking(csp, var) :
    """Returns True if var should be enqueued under the forward-checking
    condition, otherwise False"""
    return False

#### PART 6: GENERIC CSP SOLVER

def solve_constraint_generic(problem, enqueue_condition=None) :
    """Solves the problem, calling propagate with the specified enqueue
    condition (a function).  If enqueue_condition is None, uses DFS only.
    Same return type as solve_constraint_dfs."""

    agenda = [problem]
    extension_count = 0

    while agenda != []:
        current_problem = agenda.pop(0)
        extension_count +=1
        
        if not has_empty_domains(current_problem) and check_all_constraints(current_problem):
            if current_problem.unassigned_vars == []:
                return (current_problem.assigned_values, extension_count)
            
            unassigned_var = current_problem.pop_next_unassigned_var()
            
            new_problems =  [current_problem.copy().set_assigned_value(unassigned_var,val) for val in current_problem.get_domain(unassigned_var)]

            if enqueue_condition != None:
                map(lambda csp: propagate(enqueue_condition,csp,[unassigned_var]), new_problems)
            
            agenda = new_problems + agenda 

    # completely unsolvable then
    return (None, extension_count)
        
    


    
# QUESTION 5: How many extensions does it take to solve the Pokemon problem
#    with DFS and forward checking, but no propagation? (Don't use domain
#    reduction before solving it.)

ANSWER_5 = 9


#### PART 7: DEFINING CUSTOM CONSTRAINTS

def constraint_adjacent(m, n) :
    """Returns True if m and n are adjacent, otherwise False.
    Assume m and n are ints."""
    return abs(m-n) == 1

def constraint_not_adjacent(m, n) :
    """Returns True if m and n are NOT adjacent, otherwise False.
    Assume m and n are ints."""
    return abs(m-n) != 1

def all_different(variables) :
    """Returns a list of constraints, with one difference constraint between
    each pair of variables."""
    variable_pairs  = []
    for var1 in variables:
        for var2 in variables:
            if var1!= var2 and (var2,var1) not in variable_pairs:
                variable_pairs.append((var1,var2))

    return map(lambda (var1,var2): Constraint(var1,var2,constraint_different),variable_pairs)
        
    
    


#### PART 8: MOOSE PROBLEM (OPTIONAL)

moose_problem = ConstraintSatisfactionProblem(["You", "Moose", "McCain",
                                               "Palin", "Obama", "Biden"])

# Tweak Part 7 functions
def constraint_adjacent_moose_problem(m,n):
    return abs(m-n) ==1 or abs(m-n) ==5

def constraint_not_adjacent_moose_problem(m,n):
    return not constraint_adjacent_moose_problem(m,n)

# Add domains and constraints to your moose_problem here:
# Domain
regular_domain = [1,2,3,4,5,6]
moose_problem.set_domain("Moose",regular_domain)
moose_problem.set_domain("McCain",[1])
moose_problem.set_domain("Palin",regular_domain)
moose_problem.set_domain("Obama",regular_domain)
moose_problem.set_domain("Biden",regular_domain)
moose_problem.set_domain("You",regular_domain)

# Constraints
moose_problem.add_constraints(all_different(moose_problem.get_all_variables()))


moose_problem.add_constraint("Palin","McCain",constraint_adjacent_moose_problem)
moose_problem.add_constraint("Biden","Obama",constraint_adjacent_moose_problem)

moose_problem.add_constraint("McCain","Obama",constraint_not_adjacent_moose_problem)
moose_problem.add_constraint("McCain","Biden",constraint_not_adjacent_moose_problem)
moose_problem.add_constraint("Palin","Obama",constraint_not_adjacent_moose_problem)
moose_problem.add_constraint("Palin","Biden",constraint_not_adjacent_moose_problem)

moose_problem.add_constraint("Moose","Palin",constraint_not_adjacent_moose_problem)




# To test your moose_problem AFTER implementing all the solve_constraint
# methods above, change TEST_MOOSE_PROBLEM to True:
TEST_MOOSE_PROBLEM = True


#### SURVEY ###################################################

NAME = None
COLLABORATORS = None
HOW_MANY_HOURS_THIS_LAB_TOOK = None
WHAT_I_FOUND_INTERESTING = None
WHAT_I_FOUND_BORING = None
SUGGESTIONS = None


###########################################################
### Ignore everything below this line; for testing only ###
###########################################################

if TEST_MOOSE_PROBLEM:
    # These lines are used in the local tester iff TEST_MOOSE_PROBLEM is True
    moose_answer_dfs = solve_constraint_dfs(moose_problem.copy())
    moose_answer_propany = solve_constraint_propagate_reduced_domains(moose_problem.copy())
    moose_answer_prop1 = solve_constraint_propagate_singleton_domains(moose_problem.copy())
    moose_answer_generic_dfs = solve_constraint_generic(moose_problem.copy(), None)
    moose_answer_generic_propany = solve_constraint_generic(moose_problem.copy(), condition_domain_reduction)
    moose_answer_generic_prop1 = solve_constraint_generic(moose_problem.copy(), condition_singleton)
    moose_answer_generic_fc = solve_constraint_generic(moose_problem.copy(), condition_forward_checking)
    moose_instance_for_domain_reduction = moose_problem.copy()
    moose_answer_domain_reduction = domain_reduction(moose_instance_for_domain_reduction)
    moose_instance_for_domain_reduction_singleton = moose_problem.copy()
    moose_answer_domain_reduction_singleton = domain_reduction_singleton_domains(moose_instance_for_domain_reduction_singleton)


### for debugging purposes
m = get_pokemon_problem()
