import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random
import math
import operator

class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__ ( self, gb, trail, val_sh, var_sh, cc ):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck ( self ):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    """
        Part 1 TODO: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Note: remember to trail.push variables before you assign them
        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """
    def forwardChecking ( self ):
        returnDict = {}

        for v in self.network.getVariables():
            if v.isAssigned():
                for vNeighbor in self.network.getNeighborsOfVariable(v): # vNeighbor is a list of all variables that share a constraint with v
                    vNeighborDomain = vNeighbor.getDomain()
                    if vNeighborDomain.contains(v.getAssignment()):
                        self.trail.push(vNeighbor)
                        vNeighbor.removeValueFromDomain(v.getAssignment())
                        returnDict[vNeighbor] = vNeighbor.getDomain()
                        if vNeighborDomain.size() == 0:
                            return (returnDict,False)

        return (returnDict,self.network.isConsistent())

    # =================================================================
	# Arc Consistency
	# =================================================================
    def arcConsistency( self ):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

    
    """
        Part 2 TODO: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Note: remember to trail.push variables before you assign them
        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """
    def norvigCheck ( self ):
        returnDict = dict()

        for v in self.network.getVariables():
            if v.isAssigned():
                for vNeighbor in self.network.getNeighborsOfVariable(v): # vNeighbor is a list of all variables that share a constraint with v
                    vNeighborDomain = vNeighbor.getDomain()
                    if vNeighborDomain.contains(v.getAssignment()):
                        self.trail.push(vNeighbor)
                        vNeighbor.removeValueFromDomain(v.getAssignment())
                        returnDict[vNeighbor] = vNeighbor.getDomain()
                        if vNeighborDomain.size() == 0:
                            return (returnDict,False)
            else: # v not assigned
                if v.getDomain().size() == 1:
                    self.trail.push(v)
                    v.assignValue(v.getDomain().values[0])
                    returnDict[v] = v.getAssignment()
                    consistent = self.network.isConsistent()
                    if not consistent:
                        return ({},False)

        #########################

        for constraint in self.network.getConstraints():
            counterArray = [0 for i in range(self.gameboard.N)]
            variableArray = [None for i in range(self.gameboard.N)]
            for constraintVar in constraint.vars:
                for value in constraintVar.getDomain().values:
                    variableArray[value - 1] = constraintVar
                    counterArray[value - 1] += 1
            for i in range(1, self.gameboard.N + 1): # 1 - 9
                if counterArray[i - 1] == 0:
                    return (returnDict, False)
                elif counterArray[i - 1] == 1 and not variableArray[i - 1].isAssigned():
                    self.trail.push(variableArray[i - 1])
                    variableArray[i - 1].assignValue(i)
                    returnDict[variableArray[i - 1]] = i
                    consistent = self.network.isConsistent()
                    if not consistent:
                        return ({},False)
        return (returnDict, self.network.isConsistent())


    """
         Optional TODO: Implement your own advanced Constraint Propagation

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournCC ( self ):
        return False

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable ( self ):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    """
        Part 1 TODO: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """
    def getMRV ( self ):
        min = math.inf
        minVariable = None
        for v in self.network.variables:
            if v.domain.size() < min and not v.isAssigned():
                min = v.domain.size()
                minVariable = v
        return minVariable

    """
        Part 2 TODO: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the  most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """
    def MRVwithTieBreaker ( self ):
        smallestDomainList = [None]
        min = math.inf
        for v in self.network.variables:
            if v.domain.size() < min and not v.isAssigned():
                min = v.domain.size()
                smallestDomainList = []
                smallestDomainList.append(v)
            elif v.domain.size() == min and not v.isAssigned():
                smallestDomainList.append(v)

        if len(smallestDomainList) > 1:
            for v in smallestDomainList:
                dictionary = {}
                counter = 0
                for vNeighbor in self.network.getNeighborsOfVariable(v):
                    affected = False
                    for value in v.domain.values:
                        if vNeighbor.domain.contains(value):
                            affected = True
                    if affected:
                        counter += 1
                dictionary[v] = counter

            sortedListOfTuples = sorted(dictionary.items(), key=operator.itemgetter(1))
            while (sortedListOfTuples[0][1] != sortedListOfTuples[-1][1]):
                sortedListOfTuples.pop(0)
            return [key for key,value in sortedListOfTuples]

        else:
            return smallestDomainList

    """
         Optional TODO: Implement your own advanced Variable Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVar ( self ):
        return None

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    """
        Part 1 TODO: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """
    def getValuesLCVOrder ( self, v ):
        dictionary = {}
        for value in v.domain.values:
            counter = 0
            for vNeighbor in self.network.getNeighborsOfVariable(v):
                if vNeighbor.domain.contains(value):
                    counter += 1
            dictionary[value] = counter

        sortedListOfTuples = sorted(dictionary.items(), key=operator.itemgetter(1))
        return [key for key,value in sortedListOfTuples]

    """
         Optional TODO: Implement your own advanced Value Heuristic

         Completing the three tourn heuristic will automatically enter
         your program into a tournament.
     """
    def getTournVal ( self, v ):
        return None

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve ( self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if ( v == None ):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues( v ):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push( v )

            # Assign the value
            v.assignValue( i )

            # Propagate constraints, check consistency, recur
            if self.checkConsistency():
                elapsed_time = time.time() - start_time 
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1
                
            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()
        
        return 0

    def checkConsistency ( self ):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking()[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck()[1]

        if self.cChecks == "tournCC":
            return self.getTournCC()

        else:
            return self.assignmentsCheck()

    def selectNextVariable ( self ):
        if self.varHeuristics == "MinimumRemainingValue":
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            return self.MRVwithTieBreaker()[0]

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues ( self, v ):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder( v )

        if self.valHeuristics == "tournVal":
            return self.getTournVal( v )

        else:
            return self.getValuesInOrder( v )

    def getSolution ( self ):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
