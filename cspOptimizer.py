import cspConsistency
import cspProblem
import searchGeneric
import searchProblem
import sys
import io

# Days are defined by intervals of 8 starting at 1
# The day time is determined by adding day + time - 1 (used in later functions)
# Dictionaries go two ways to facilitate easy conversion
daydict = {
    "mon" : 1,
    "tue" : 9,
    "wed" : 17,
    "thu" : 25,
    "fri" : 33,
    1 : "mon",
    9 : "tue",
    17 : "wed",
    25 : "thu",
    33 : "fri"
}

timedict = {
    "9am" : 1,
    "10am" : 2,
    "11am" : 3,
    "12pm" : 4,
    "1pm" : 5,
    "2pm" : 6,
    "3pm" : 7,
    "4pm" : 8,
    1 : "9am",
    2 : "10am",
    3 : "11am",
    4 : "12pm",
    5 : "1pm",
    6 : "2pm",
    7 : "3pm",
    8 : "4pm"
}


# Extended class to override heuristic and add_to_frontier
class AStarSearcher(searchGeneric.AStarSearcher):
    """returns a searcher for a problem.
    Paths can be found by repeatedly calling search().
    """
    max_display_level = 0
    
        
    def empty_frontier(self):
        return self.frontier.empty()

    def add_to_frontier(self,path):
        """add path to the frontier with the appropriate cost"""
        # Removed the other component as there is no "movement" cost with the arcs
        value = self.problem.heuristic(path.end())
        self.frontier.add(path, value)
    def heuristic(self, node):
        return problem.heuristic
# Overrided to include soft domains and heuristic
class CSP(cspProblem.CSP):
    def __init__(self, domains, constraints, soft_domains):
        super().__init__(domains, constraints)
        soft_domains = soft_domains
    # Returns associated heuristic cost given node
    def heuristic(self, node):
        cost = 0
        # Iterates through every meeting
        for meeting in node:
            times = node[meeting]
            # Checks if there is 1 time only
            # We don't calculate the cost if there are multiple times
            if len(times) != 1:
                return 0
            time = list(times)[0]
            # Prevents an error when an invalid dictionary key is used
            if soft_domains[meeting] == None:
                continue
            # early-week case
            if time > 9:
                if "early-week" in soft_domains[meeting]:
                    # Adds the count of days after Monday to cost
                    count = Day_Count(time)
                    cost += count
            # late-week case
            if time < 33:
                if "late-week" in soft_domains[meeting]:
                    # Subtracts the days after Monday from 4 and adds the result to cost
                    count = Day_Count(time)
                    cost += (4 - count)
            # early-morning case
            if "early-morning" in soft_domains[meeting]:
                # Iterates to the correct day and adds the
                # distance from 9am to cost
                i = 0
                while i < 41:
                    if time > i and time < i + 9:
                        cost += (time - i - 1)
                    i += 8
            # midday case
            if "midday" in soft_domains[meeting]:
                # Iterates to the correct day and adds the
                # distance from 12pm to cost
                i = 0
                while i < 41:
                    # before 12
                    if time > i and time < i + 4:
                        cost += (i + 4) - time
                    # after 12
                    if time > i + 4 and time < i + 9:
                        cost += time - (i + 4)
                    i += 8
            # late-afternoon case
            if "late-afternoon" in soft_domains[meeting]:
                # Iterates to the correct day and adds the
                # distance from 4pm to cost
                i = 0
                while i < 41:
                    if time > i and time < i + 9:
                        cost += (i + 8) - time
                    i += 8
        return cost

# Extends a heuristic function to the search
class Search_with_AC_from_Cost_CSP(cspConsistency.Search_with_AC_from_CSP):  
    def heuristic(self, n):
        return self.cons.csp.heuristic(n)


# Constraint Functions
def Before(ass1, ass2):
    return ass1 < ass2
def SameDay(ass1, ass2):
    # Iterates to the day of ass1 and checks if ass2 is within range
    i = 0
    while i < 41:
        if ass1 > i and ass1 < i + 9:
            if ass2 > i and ass2 < i + 9:
                return True        
        i += 8
    return False
def OneDayBetween(ass1, ass2):
    # Checks if either ass1 is a day ahead of ass2 or vice versa
    i = 0
    while i < 41:
        if ass1 > i and ass1 < i + 9:
            if ass2 > i and ass2 < i + 9:
                return False        
            if ass2 > i + 8 and ass2 < i + 17:
                return False
        if ass2 > i and ass2 < i + 9:
            if ass1 > i and ass1 < i + 9:
                return False
            if ass1 > i + 8 and ass1 < i + 17:
                return False
        i += 8
    return True
def OneHourBetween(ass1, ass2):
    return abs(ass1 - ass2) > 1

# Extra constraint added to all meetings to prevent double ups
def NotEqual(ass1, ass2):
    return not ass1 == ass2

# Returns count of days after Monday
def Day_Count(time):
    count = 0
    timecopy = time
    while timecopy > 8:
        count += 1
        timecopy -= 8
    return count

# Used to declutter the main and handle constraint cases
def Constraint(line):
    # Create constraint object in cspProblem
    segments = line.split()
    scope = (segments[1], segments[3])
    if (segments[2] == "before"):
        condition = Before
    elif(segments[2] == "one-day-between"):
        condition = OneDayBetween
    elif(segments[2] == "same-day"):
        condition = SameDay
    elif(segments[2] == "one-hour-between"):
        condition = OneHourBetween
    CurrConstraint = cspProblem.Constraint(scope, condition)
    return CurrConstraint


file = sys.argv[1]
if file == "-f":
    input_file = open('binary/one-hour-between-1.in', 'r')
else:
    input_file = open(file, 'r')
sys.stdin = io.StringIO(input_file.read())

# Read in stdin, ignoring comments into a string array
domains = {};
soft_domains = {};
constraints = list();
for line in sys.stdin:
    if line[0] == "#":
        pass
    else:
        # Initialises a meetings domains and soft_domains
        if line.find("meeting", 0, 7) == 0:
            # Creates the domain as 1 to 40
            domains[line[9:].strip()] = list(range(1, 41))
            soft_domains[line[9:].strip()] = list()
        # Creates a new constraint handled by function
        elif line.find("constraint", 0, 10) == 0:
            constraints.append(Constraint(line))
        # Case for soft or hard domains
        elif line.find("domain", 0, 6) == 0:
            # soft domain case
            if line.find("soft") != -1:
                # Gets the meeting and the condition
                # and appends the condition to the meetings soft domains
                line.strip()
                segments = line.split(',')
                currElem = segments[1].strip()
                cond = segments[2].strip()
                soft_domains[currElem].append(cond)              
            elif line.find("hard") != -1:
                line.strip()
                segments = line.split(',')
                # Gets the current meeting
                currElem = segments[1].strip()
                # Gets the conditions
                conds = segments[2].strip()
                # fullconds used for multi word conditions e.g. before mon
                fullconds = conds.split(' ')
                # lenconds used to check conditions
                lenconds = len(fullconds)
                # <day> case
                if conds in daydict and lenconds == 1:
                    # Delete all before and after that day
                    i = daydict[fullconds[0]]
                    j = 1
                    while j < i:
                        if j in domains[currElem]:
                            domains[currElem].remove(j)
                        j += 1
                    j = i + 8
                    while j <= 40:
                        if j in domains[currElem]:
                            domains[currElem].remove(j)
                        j += 1
                # <time> case
                elif conds in timedict:
                    # Gets the intersection of the valid time for each day as the new domain
                    x = timedict[conds]
                    validTimeList = (x, x + 8, x + 16, x + 24, x + 32) 
                    domains[currElem] = list(set(domains[currElem]).intersection(validTimeList))
                # <morning> case
                elif conds == "morning":
                    # Gets the intersection of the valid time for each day as the new domain
                    validTimeList = [1, 2, 3, 9, 10, 11, 17, 18, 19, 25, 26, 27, 33, 34, 35]
                    domains[currElem] = list(set(domains[currElem]).intersection(validTimeList))
                elif conds == "afternoon":
                    # Gets the intersection of the valid time for each day as the new domain
                    validTimeList = [4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 20, 21, 22, 23, 24, 28, 29, 30, 31, 32, 36, 37, 38, 39, 40]
                    domains[currElem] = list(set(domains[currElem]).intersection(validTimeList))

                # <before> case
                elif "before" in conds:
                    # day
                    if fullconds[1] in daydict and lenconds == 2:
                        # deletes all values after and including the given day
                        time = daydict[fullconds[1]]
                        j = time
                        while j < 41:
                            if j in domains[currElem]:
                                domains[currElem].remove(j)
                            j += 1
                    # time
                    elif fullconds[1] in timedict and lenconds == 2:
                        # Gets the intersection of the valid time for each day as the new domain
                        z = timedict[fullconds[1]]
                        validTimeList = list(range(1, z)) + list(range(9, z + 8)) + list(range(17, z + 16)) + list(range(25, z + 24))+ list(range(33, z + 32))
                        domains[currElem] = list(set(domains[currElem]).intersection(validTimeList))
                    # day time
                    elif lenconds == 3:
                        # deletes all after and including the given day time
                        x = daydict[fullconds[1]]
                        y = timedict[fullconds[2]]
                        # Adjusting as day + time is 1 more than required
                        time = x + y - 1
                        j = time
                        while j < 41:
                            if j in domains[currElem]:
                                domains[currElem].remove(j)
                            j += 1
                # <after> case
                elif "after" in conds and "afternoon" not in conds:
                    fullconds = conds.split(' ')
                    lenconds = len(fullconds)
                    # day
                    if fullconds[1] in daydict and lenconds == 2:
                        # deletes all values before and during given day
                        j = 0
                        while j < daydict[fullconds[1]] + 8:
                            if j in domains[currElem]:
                                domains[currElem].remove(j)
                            j += 1
                    # time
                    elif fullconds[1] in timedict and lenconds == 2:
                        # Gets the intersection of the valid time for each day as the new domain
                        z = timedict[fullconds[1]]
                        validTimeList = list(range(z , 8)) + list(range(z + 8, 16)) + list(range(z + 16, 24)) + list(range(z + 24, 32))+ list(range(z + 32, 40))
                        domains[currElem] = list(set(domains[currElem]).intersection(validTimeList))
                    # day time
                    elif lenconds == 3:
                        # deletes all values before and during given day time
                        x = daydict[fullconds[1]]
                        y = timedict[fullconds[2]]
                        time = x + y
                        j = 0
                        while j < time:
                            if j in domains[currElem]:
                                domains[currElem].remove(j)
                            j += 1
                # <day time-day time> case
                elif lenconds == 3:
                    # splits the - in the middle
                    part2 = fullconds[1].split('-')
                    # deletes values before lower bound and after upper bound
                    time = daydict[fullconds[0]] + timedict[part2[0]] - 1
                    j = 0
                    while j < time:
                        if j in domains[currElem]:
                            domains[currElem].remove(j)
                        j += 1
                    after = daydict[part2[1]] + timedict[fullconds[2]]
                    j = after
                    while j < 41:
                        if j in domains[currElem]:
                            domains[currElem].remove(j)
                        j += 1
                        
# convert to set to work with the other functions and prevent equal values
for each in domains:
    domains[each] = set(domains[each])
    for every in domains:
        if each == every:
            continue
        else:
            scope = (each, every)
            constraints.append(cspProblem.Constraint(scope, NotEqual))
# Creates CSP object
csproblem = CSP(domains, constraints, soft_domains)
# Creates SearchProblem
SearchProblem = Search_with_AC_from_Cost_CSP(csproblem)
# Creates Solver
Solver = AStarSearcher(SearchProblem)
# Starts the search
Solver.search()
# Checks if there is a solution
if hasattr(Solver, "solution"):
    # Check for when the initial is the answer and there is no arc
    if Solver.solution.arc != None:
        # for all elements, convert the integer into a daytime
        for elem in Solver.solution.arc.to_node:
            Copy = Solver.solution.arc.to_node[elem]
            Assignment = str(Copy).strip('{}')
            Assignment = int(Assignment)

            Day = 0
            while Assignment > 8:
                Assignment -= 8
                Day += 1
            print(elem + ":" + daydict[1 + Day * 8] + " " + timedict[Assignment])
        # Calculate and print the cost
        print("cost:" + str(csproblem.heuristic(Solver.solution.arc.to_node)))
    else:
        # for all elements, convert the integer into a daytime
        for elem in Solver.solution.initial:
            Copy = Solver.solution.initial[elem]
            Assignment = str(Copy).strip('{}')
            Assignment = int(Assignment)

            Day = 0
            while Assignment > 8:
                Assignment -= 8
                Day += 1
            print(elem + ":" + daydict[1 + Day * 8] + " " + timedict[Assignment])
        # Calculate and print the cost
        print("cost:" + str(csproblem.heuristic(Solver.solution.initial)))
# No solution found prints No solution
else:
    print("No solution")


