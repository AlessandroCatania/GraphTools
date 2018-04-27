from collections import *
from namedlist import namedlist

from copy import deepcopy
import  itertools
import itertools


Street = namedtuple('Street', 'StreetName start end')
Coordinate = namedtuple('Coordinate', 'x y')
EdgeLabel = namedtuple('EdgeLabel', 'streetStretch Coordinate stepCost')
frontierObj = namedlist('frontierObj', 'Coordinate stepCost')
Frontier = namedlist('Frontier', 'nodeObj cost')
Children = namedlist('Children','Parent Child')
Node = namedlist('Node','Parent State stepCost')
filename = "Paths.txt"

def get_street_name(coord1, coord2, street_info):
    for i in street_info:
        if (i.start == coord1 and i.end == coord2):
            return i.StreetName


def calcCost(Node1, Node2):
    return ((Node1[0] - Node2[0])**2 + (Node1[1] - Node2[1])**2)**0.5


def isLineEmpty(line):
    return len(line.strip()) == 0


def readPaths(filename):
    Paths = []
    with open(filename) as paths:
        for line in paths:
            if not isLineEmpty(line):
                Paths.append(line.replace("\n", ""))
    return Paths


def parsePaths(paths):
    (x1, x2, SC, x3, x4) = paths.split(' ')
    Start = (int(x1), int(x2))
    StreetLabel = SC
    End = (int(x3), int(x4))
    return (Start, StreetLabel, End)


def pairwise(lst):
    if not lst:
        return
    i = 0
    while i < (len(lst) - 1):
        yield lst[i], lst[i + 1]
        i += 2


def initialize_street_information():
    street_info = []
    with open(filename) as paths:
        for line in paths:
            entry = line.rstrip('\n').split(' ')
            if len(entry) == 5:
                street_info.append(Street(StreetName=entry[2], 
                	start=Coordinate(x=int(entry[0]), y=int(entry[1])), 
                	end=Coordinate(x=int(entry[3]), y=int(entry[4]))))
    return street_info


def extract_coordinates():
	street_info = initialize_street_information()
	coordinate_set = set()
	for i in street_info:
		coordinate_set.add(i.start)
		coordinate_set.add(i.end)
	return coordinate_set


def print_directions(explored, end):
    street_info = initialize_street_information()
    print(explored)
    explored.append(end)
    print('Directions...')
    for start, end in pairwise(explored):
        print('Walk from {} through {} to get to {}'.format(
            start, get_street_name(start, end, street_info), end))


def print_directions2(explored, end):
    street_info = initialize_street_information()
    print(explored)
    print('Directions...')
    for node in explored:
        print('Walk from {} through {} to get to {}'.format(
            node.Parent, get_street_name(node.Parent, node.State, street_info), node.State))


def readPaths(filename):
    Paths = []
    with open(filename) as paths:
        for line in paths:
            if not isLineEmpty(line):
                Paths.append(line.replace("\n", ""))
    return Paths


def extract_coordinates():
    street_info = initialize_street_information()
    coordinate_set = set()
    for i in street_info:
        coordinate_set.add(i.start)
        coordinate_set.add(i.end)
    return coordinate_set


def parseKB(kbList):
    for i in range(0, len(kbList)):
        kbList[i] = kbList[i].replace(' ', '').split("IF")

        if len(kbList[i]) == 1:
            kbList[i].append([])
        else:
            kbList[i][1] = kbList[i][1].split(',')
            kbNotSplit = kbList[i][0].split(negsymbol)

            kbList[i][0] = negation(kbNotSplit)

    expDistribution(kbList)

    return kbList


def negation(splittedEntry):
    if ((len(splittedEntry) - 1) % 2 == 0):
        final = ''
        for k in splittedEntry:
            if k != negsymbol:
                final += k
        return negsymbol + ' ' + final
    return splittedEntry.pop()


def genResolution(kbList,negSymbol,toProve):
    toProve = negation(toProve.split(negSymbol))
    kbList.append(toProve)
    return kbList


def expDistribution(kbList):
    for i in range(0,len(kbList)):
        if(len(kbList[i][1])>1):
            #Entire array
            test = kbList[i][1]
            entry = kbList[i]
            kbList.pop(i) # Removing the entry from kbList
            for j in range(0, len(entry[1])):
                newEntry = [entry[0], [entry[1][j]]]
                if newEntry not in kbList:
                    kbList.insert(i, newEntry) # adding a new entry for each individual RHS item in kbList entry
    return kbList


def negateList(posList):
    negList = []
    for i in posList:
        negList.append(negation([i]))
    return negList


def removeRNOT(symbol): # Removes Redundant NOT symbols
    condensed = symbol.split("NOT ")
    if (len(condensed)%2 == 0):
        return 'NOT ' + condensed[-1]
    else:
        return condensed[-1]


def removeRNOTlist(List):
    notList = []
    for i in range(0,len(List)):
        notList.append(removeRNOT(List[i]))
    return notList


def negateKB(KBlist):
    negatedList = []
    for i in KBlist:
        x = negateList(i)
        y = removeRNOTlist(x)
        negatedList.append(y)
    return negatedList


def simplifyKB(KB):
    simpleKB = []
    for i in KB:
        if (len(i[1]) > 0):
            store = [i[0],i[1][0]]
        else:
            store = [i[0]]
        simpleKB.append(store)
    return simpleKB


def resolvePair(Ci,Cj):
    Ci_new = Ci
    Cj_new = Cj
    resolvedClause = []
    negatedCj = removeRNOTlist(negateList(Cj))
    resolvedElements = set(Ci).intersection(negatedCj)
    for i in resolvedElements:
        Ci_new.remove(i)
        j = removeRNOT('NOT ' + i)
        Cj_new.remove(j)
    if len(resolvedElements) > 0:
        resolvedClause.extend(Ci_new)
        resolvedClause.extend(Cj_new)
    else:
        return False
    return list(set(resolvedClause)) # Removing duplicates


def Resolution(rules):
    newClauses = []
    for i in range(0, len(rules)):
        for j in range(0, len(rules)):
            if i < j:
                Clause1 = deepcopy(rules[i])
                Clause2 = deepcopy(rules[j])
                resolved = resolvePair(Clause1, Clause2)
                if resolved != False and resolved not in newClauses:
                    newClauses.append(resolved)
    return newClauses


def matchNegThesis(clause, goal):
    return len(goal) - len(set(clause).intersection(goal))


def clauseCost(resolvedClauses, thesis):
    costList = []
    neg_thesis = removeRNOTlist(negateList(thesis))
    for i in resolvedClauses:
        score = matchNegThesis(i, neg_thesis)
        costList.append(score)
    return costList


def createNode(currKB,newClause,stepCost):
    parentState = currKB
    childState = deepcopy(currKB)
    childState.append(newClause)
    childNode = Node(Parent=currKB,State=childState,stepCost=stepCost)
    return childNode


def expand(currKB):
    Children = []
    stepCost = 1
    possClauses = Resolution(deepcopy(currKB))
    for i in possClauses:
        child = createNode(deepcopy(currKB),i,stepCost)
        Children.append(child)
    return Children


def goalTest(testList):
    for i in testList:
        if i == []:
            return True
    return False


KB = readPaths('KB2.txt')
negsymbol = 'NOT'


KB = parseKB(KB)
print(KB)
# KB = expDistribution(KB)
# KB = resolutionAlgorithm(KB)
print(KB)


testList1 = ['bu','NOT fo','te']
# negateList(KB)
simpleKB = simplifyKB(KB)
checker = 'NOT NOT NOT NOT NOT fo'
print(simpleKB)
testList2 = ['bu','NOT fo']


RULES = simpleKB
toProve = ['NOT R']
RULES.append(toProve)


y = Resolution(deepcopy(RULES))
#print(y)
thesis = ['NOT R','NOT Q']
print(y)
print(clauseCost(y,thesis))
testing = expand(deepcopy(RULES))
for i in range(0,len(testing)):
    print('Child ',i,': ',testing[i])


