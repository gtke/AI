# Giorgi Tkeshelashvili

from collections import deque

"""
	Base class for unary constraints
	Implement isSatisfied in subclass to use
"""
class UnaryConstraint:
	def __init__(self, var):
		self.var = var

	def isSatisfied(self, value):
		util.raiseNotDefined()

	def affects(self, var):
		return var == self.var


"""	
	Implementation of UnaryConstraint
	Satisfied if value does not match passed in paramater
"""
class BadValueConstraint(UnaryConstraint):
	def __init__(self, var, badValue):
		self.var = var
		self.badValue = badValue

	def isSatisfied(self, value):
		return not value == self.badValue

	def __repr__(self):
		return 'BadValueConstraint (%s) {badValue: %s}' % (str(self.var), str(self.badValue))


"""	
	Implementation of UnaryConstraint
	Satisfied if value matches passed in paramater
"""
class GoodValueConstraint(UnaryConstraint):
	def __init__(self, var, goodValue):
		self.var = var
		self.goodValue = goodValue

	def isSatisfied(self, value):
		return value == self.goodValue

	def __repr__(self):
		return 'GoodValueConstraint (%s) {goodValue: %s}' % (str(self.var), str(self.goodValue))


"""
	Base class for binary constraints
	Implement isSatisfied in subclass to use
"""
class BinaryConstraint:
	def __init__(self, var1, var2):
		self.var1 = var1
		self.var2 = var2

	def isSatisfied(self, value1, value2):
		# to be implemented
		util.raiseNotDefined()

	def affects(self, var):
		return var == self.var1 or var == self.var2

	def otherVariable(self, var):
		if var == self.var1:
			return self.var2
		return self.var1


"""
	Implementation of BinaryConstraint
	Satisfied if both values assigned are different
"""
class NotEqualConstraint(BinaryConstraint):
	def isSatisfied(self, value1, value2):
		if value1 == value2:
			return False
		return True

	def __repr__(self):
	    return 'NotEqualConstraint (%s, %s)' % (str(self.var1), str(self.var2))


class ConstraintSatisfactionProblem:
	"""
	Structure of a constraint satisfaction problem.
	Variables and domains should be lists of equal length that have the same order.
	varDomains is a dictionary mapping variables to possible domains.

	Args:
		variables (list<string>): a list of variable names
		domains (list<set<value>>): a list of sets of domains for each variable
		binaryConstraints (list<BinaryConstraint>): a list of binary constraints to satisfy
		unaryConstraints (list<UnaryConstraint>): a list of unary constraints to satisfy
	"""
	def __init__(self, variables, domains, binaryConstraints = [], unaryConstraints = []):
		self.varDomains = {}
		for i in xrange(len(variables)):
			self.varDomains[variables[i]] = domains[i]
		self.binaryConstraints = binaryConstraints
		self.unaryConstraints = unaryConstraints

	def __repr__(self):
	    return '---Variable Domains\n%s---Binary Constraints\n%s---Unary Constraints\n%s' % ( \
	        ''.join([str(e) + ':' + str(self.varDomains[e]) + '\n' for e in self.varDomains]), \
	        ''.join([str(e) + '\n' for e in self.binaryConstraints]), \
	        ''.join([str(e) + '\n' for e in self.unaryConstraints]))


class Assignment:
	"""
	Representation of a partial assignment.
	Has the same varDomains dictionary stucture as ConstraintSatisfactionProblem.
	Keeps a second dictionary from variables to assigned values, with None being no assignment.

	Args:
		csp (ConstraintSatisfactionProblem): the problem definition for this assignment
	"""
	def __init__(self, csp):
		self.varDomains = {}
		for var in csp.varDomains:
			self.varDomains[var] = set(csp.varDomains[var])
		self.assignedValues = { var: None for var in self.varDomains }

	"""
	Determines whether this variable has been assigned.

	Args:
		var (string): the variable to be checked if assigned
	Returns:
		boolean
		True if var is assigned, False otherwise
	"""
	def isAssigned(self, var):
		return self.assignedValues[var] != None

	"""
	Determines whether this problem has all variables assigned.

	Returns:
		boolean
		True if assignment is complete, False otherwise
	"""
	def isComplete(self):
		for var in self.assignedValues:
			if not self.isAssigned(var):
				return False
		return True

	"""
	Gets the solution in the form of a dictionary.

	Returns:
		dictionary<string, value>
		A map from variables to their assigned values. None if not complete.
	"""
	def extractSolution(self):
		if not self.isComplete():
			return None
		return self.assignedValues

	def __repr__(self):
	    return '---Variable Domains\n%s---Assigned Values\n%s' % ( \
	        ''.join([str(e) + ':' + str(self.varDomains[e]) + '\n' for e in self.varDomains]), \
	        ''.join([str(e) + ':' + str(self.assignedValues[e]) + '\n' for e in self.assignedValues]))



####################################################################################################


"""
	Checks if a value assigned to a variable is consistent with all binary constraints in a problem.
	Do not assign value to var. Only check if this value would be consistent or not.
	If the other variable for a constraint is not assigned, then the new value is consistent with the constraint.
	You do not have to consider unary constraints, as those have already been taken care of.

	Args:
		assignment (Assignment): the partial assignment
		csp (ConstraintSatisfactionProblem): the problem definition
		var (string): the variable that would be assigned
		value (value): the value that would be assigned to the variable
	Returns:
		boolean
		True if the value would be consistent with all currently assigned values, False otherwise
"""
def consistent(assignment, csp, var, value):
	for constraint in csp.binaryConstraints:
		if constraint.affects(var):
			if assignment.isAssigned(constraint.otherVariable(var)):
				if not constraint.isSatisfied(value, assignment.assignedValues[constraint.otherVariable(var)]):
					return False
	return True

"""
	Recursive backtracking algorithm.
	A new assignment should not be created. The assignment passed in should have its domains updated with inferences.
	In the case that a recursive call returns failure or a variable assignment is incorrect, the inferences made along
	the way should be reversed. See maintainArcConsistency and forwardChecking for the format of inferences.

	Examples of the functions to be passed in:
	orderValuesMethod: orderValues, leastConstrainingValuesHeuristic
	selectVariableMethod: chooseFirstVariable, minimumRemainingValuesHeuristic
	inferenceMethod: noInferences, maintainArcConsistency, forwardChecking

	Args:
		assignment (Assignment): a partial assignment to expand upon
		csp (ConstraintSatisfactionProblem): the problem definition
		orderValuesMethod (function<assignment, csp, variable> returns list<value>): a function to decide the next value to try
		selectVariableMethod (function<assignment, csp> returns variable): a function to decide which variable to assign next
		inferenceMethod (function<assignment, csp, variable, value> returns set<variable, value>): a function to specify what type of inferences to use
			InferenceMethod will return None if the assignment has no solution. Otherwise it will return a set of inferences made. (The set can be empty.)
	Returns:
		Assignment
		A completed and consistent assignment. None if no solution exists.
"""
def recursiveBacktracking(assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod):
	if assignment.isComplete(): return assignment
	inferenceList = list()
	var = chooseFirstVariable(assignment, csp)
	for value in orderValuesMethod(assignment, csp, var):
		if consistent(assignment, csp, var, value):
			assignment.assignedValues[var] = value
			inferences = inferenceMethod(assignment, csp, var, value)
			if inferences != None:
				inferenceList.append(inferences)
				result = recursiveBacktracking(assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod)
				if result != None and result.isComplete(): return result
			for inference in inferenceList:
				for pair in inference:
					assignment.varDomains[pair[0]].add(pair[1])
			assignment.assignedValues[var] = None
	return None

"""
	Uses unary constraints to eleminate values from an assignment.

	Args:
		assignment (Assignment): a partial assignment to expand upon
		csp (ConstraintSatisfactionProblem): the problem definition
	Returns:
		Assignment
		An assignment with domains restricted by unary constraints. None if no solution exists.
"""
def eliminateUnaryConstraints(assignment, csp):
	domains = assignment.varDomains
	for var in domains:
		for constraint in (c for c in csp.unaryConstraints if c.affects(var)):
			for value in (v for v in list(domains[var]) if not constraint.isSatisfied(v)):
				domains[var].remove(value)
				if len(domains[var]) == 0:
					# Failure due to invalid assignment
					return None
	return assignment


"""
	Trivial method for choosing the next variable to assign.
	Uses no heuristics.
"""
def chooseFirstVariable(assignment, csp):
	for var in csp.varDomains:
		if not assignment.isAssigned(var):
			return var


"""
	Selects the next variable to try to give a value to in an assignment.
	Uses minimum remaining values heuristic to pick a variable. Use degree heuristic for breaking ties.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
	Returns:
		the next variable to assign
"""
def minimumRemainingValuesHeuristic(assignment, csp):
	nextVar = None
	domains = assignment.varDomains
	values  = assignment.assignedValues
	constraints = {}
	degree_heuristics = {}

	for var in values:
		if values[var] == None:
			constraints[var] = len(domains[var])
	sorted_constraints = sorted(constraints.items(), key=lambda constraints:constraints[1])

	for pair in sorted_constraints:
		if pair[1] == sorted_constraints[0][1]:
			degree_heuristics[pair[0]] = 0
			for constraint in csp.binaryConstraints:	
				if constraint.affects(pair[0]):
					key = pair[0]
					if key in degree_heuristics:
						degree_heuristics[pair[0]] += 1
	
	degree_heuristics = sorted(degree_heuristics.items(), key=lambda degree:degree[1], reverse=True)
	nextVar = degree_heuristics[0][0]
	return nextVar

"""
	Trivial method for ordering values to assign.
	Uses no heuristics.
"""
def orderValues(assignment, csp, var):
	return list(assignment.varDomains[var])


"""
	Creates an ordered list of the remaining values left for a given variable.
	Values should be attempted in the order returned.
	The least constraining value should be at the front of the list.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
		var (string): the variable to be assigned the values
	Returns:
		list<values>
		a list of the possible values ordered by the least constraining value heuristic
"""
def leastConstrainingValuesHeuristic(assignment, csp, var):
	values = list(assignment.varDomains[var])
	constrained = list()
	sortedList = list()
	pairs = {}

	for constraint in csp.binaryConstraints:
		if constraint.affects(var):
			constrained.append(constraint.otherVariable(var))

	for value in values:
		count = 0
		for v in constrained:
			if value in assignment.varDomains[v]:
				count += 1
		pairs[value] = count

	pairs = sorted(pairs.items(), key=lambda numOfConstraints:numOfConstraints[1])
	
	for pair in pairs: sortedList.append(pair[0])

	return sortedList

"""
	Trivial method for making no inferences.
"""
def noInferences(assignment, csp, var, value):
	return set([])


"""
	Implements the forward checking algorithm.
	Each inference should take the form of (variable, value) where the value is being removed from the
	domain of variable. This format is important so that the inferences can be reversed if they
	result in a conflicting partial assignment. If the algorithm reveals an inconsistency, any
	inferences made should be reversed before ending the fuction.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
		var (string): the variable that has just been assigned a value
		value (string): the value that has just been assigned
	Returns:
		set<tuple<variable, value>>
		the inferences made in this call or None if inconsistent assignment
"""
def forwardChecking(assignment, csp, var, value):
	inferences = set([])
	domains = assignment.varDomains
	variables = domains.keys()

	for constraint in csp.binaryConstraints:
			if constraint.affects(var):
				for other in domains[constraint.otherVariable(var)]:
					if not constraint.isSatisfied(value, other):
						inferences.add((constraint.otherVariable(var), other))
				
	for key in variables:
		count = 0
		for pair in inferences:
			if key == pair[0]:
				count += 1
		if len(domains[key]) == count:
			return None
	
	for key in  variables:
		for pair in inferences:
			if key == pair[0]:
				domains[key].remove(pair[1])
				
	return inferences

"""
	Helper funciton to maintainArcConsistency and AC3.
	Remove values from var2 domain if constraint cannot be satisfied.
	Each inference should take the form of (variable, value) where the value is being removed from the
	domain of variable. This format is important so that the inferences can be reversed if they
	result in a conflicting partial assignment. If the algorithm reveals an inconsistency, any
	inferences made should be reversed before ending the fuction.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
		var1 (string): the variable with consistent values
		var2 (string): the variable that should have inconsistent values removed
		constraint (BinaryConstraint): the constraint connecting var1 and var2
	Returns:
		set<tuple<variable, value>>
		the inferences made in this call or None if inconsistent assignment
"""
def revise(assignment, csp, var1, var2, constraint):
	inferences   = set([])
	var1_domains = assignment.varDomains[var1]
	var2_domains = assignment.varDomains[var2]
	variables    = assignment.varDomains.keys()

	for value1 in var1_domains:
		flag = False
		for value2 in var2_domains:
			if constraint.isSatisfied(value1, value2):
				flag = True
		if flag is False:
			inferences.add((var1, value1))

	for var in variables:
		count = 0
		for item in inferences:
			if var == item[0]:
				count += 1
			if len(assignment.varDomains[var]) == count:
				return None

	for pair in inferences:
		temp = assignment.varDomains[pair[0]].remove(pair[1])

	return inferences


"""
	Implements the maintaining arc consistency algorithm.
	Inferences take the form of (variable, value) where the value is being removed from the
	domain of variable. This format is important so that the inferences can be reversed if they
	result in a conflicting partial assignment. If the algorithm reveals an inconsistency, and
	inferences made should be reversed before ending the fuction.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
		var (string): the variable that has just been assigned a value
		value (string): the value that has just been assigned
	Returns:
		set<<variable, value>>
		the inferences made in this call or None if inconsistent assignment
"""
def maintainArcConsistency(assignment, csp, var, value):
	inferences = set([])
	"""Hint: implement revise first and use it as a helper function"""
	"""Question 5"""
	"""YOUR CODE HERE"""

	return inferences


"""
	AC3 algorithm for constraint propogation. Used as a preprocessing step to reduce the problem
	before running recursive backtracking.

	Args:
		assignment (Assignment): the partial assignment to expand
		csp (ConstraintSatisfactionProblem): the problem description
	Returns:
		Assignment
		the updated assignment after inferences are made or None if an inconsistent assignment
"""
def AC3(assignment, csp):
	inferences = set([])
	"""Hint: implement revise first and use it as a helper function"""
	"""Question 6"""
	"""YOUR CODE HERE"""

	return assignment


"""
	Solves a binary constraint satisfaction problem.

	Args:
		csp (ConstraintSatisfactionProblem): a CSP to be solved
		orderValuesMethod (function): a function to decide the next value to try
		selectVariableMethod (function): a function to decide which variable to assign next
		inferenceMethod (function): a function to specify what type of inferences to use
		useAC3 (boolean): specifies whether to use the AC3 preprocessing step or not
	Returns:
		dictionary<string, value>
		A map from variables to their assigned values. None if no solution exists.
"""
def solve(csp, orderValuesMethod=leastConstrainingValuesHeuristic, selectVariableMethod=minimumRemainingValuesHeuristic, inferenceMethod=forwardChecking, useAC3=True):
	assignment = Assignment(csp)

	assignment = eliminateUnaryConstraints(assignment, csp)
	if assignment == None:
		return assignment

	if useAC3:
		assignment = AC3(assignment, csp)
		if assignment == None:
			return assignment

	assignment = recursiveBacktracking(assignment, csp, orderValuesMethod, selectVariableMethod, inferenceMethod)
	if assignment == None:
		return assignment

	return assignment.extractSolution()