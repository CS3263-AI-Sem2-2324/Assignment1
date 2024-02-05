"""
Assignment 1 Problem 1 programming script

* Group Member 1:
    - Name:
    - Student ID:

* Group Member 2:
    - Name:
    - Student ID:
"""

# !IMPORTANT: The following import is CORRECT for our evaluation, please DO NOT change it!
from FAIAss1CP.aimalogic4e import *


def print_kb(kb):
    for item in kb.clauses:
        print(item)


# ====== Task 1 ======

clauses = []
clauses.append(expr("Martian(Green)"))
clauses.append(expr("Rover(Persy)"))
clauses.append(expr("Friend(Green, Persy)"))

clauses.append(expr("Owns(Green, S1)"))
clauses.append(expr("Souvenir(S1)"))

# ========== Task 1: Building the KB ==========

'''---your code starts here---'''

# clauses.append(expr("..."))


'''----your code ends here----'''

print(clauses)

mars_kb = FolKB(clauses)

# ========== Task 2: Who Are My Friends?  ==========

# ========== Task 2-1: Add Good News ==========

# Add news to KB:
'''---your code starts here---'''



'''---your code ends here---'''

# ========== Task 2-2: Find Nice Martians ==========

# Forward chaining algorithm:

'''---your code starts here---'''

answer = []

'''----your code ends here----'''

print(list(answer))

mars_kb = FolKB(clauses)

# re-add the news and use backward chaining algorithm:

'''---your code starts here---'''

answer = []

'''----your code ends here----'''

print(list(answer))

# ========== Task 3: Who is the HERO? ==========

# ========== Task 3-1: Add Hero Definition ==========

'''---your code starts here---'''



'''---your code ends here---'''

# ========== Task 3-2: Find the Hero ==========

# Find Hero with Forward Chaining and Backward Chaining

'''---your code starts here---'''

answer_fc = []

answer_bc = []

'''---your code ends here---'''

print(list(answer_fc))
print(list(answer_bc))
