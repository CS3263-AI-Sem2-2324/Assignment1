"""
The solution for Problem 1.

* Group Member 1:
    - Name:
    - Student ID:


* Group Member 2:
    - Name:
    - Student ID:

"""

from FAIAss1.aimalogic4e import *


class Problem1:
    def __init__(self):
        pass

    def task1(self):
        clauses = []
        clauses.append(expr("Martian(Green)"))
        clauses.append(expr("Rover(Persy)"))
        clauses.append(expr("Friend(Green, Persy)"))
        clauses.append(expr("Owns(Green, S1)"))
        clauses.append(expr("Souvenir(S1)"))

        # --- Problem 1 Task 1: your code starts here---

        # clauses.append(expr("..."))

        # --- Problem 1 Task 1: your code ends here---

        return clauses

    def task2(self, clauses):
        # ! The `clauses` have included the clauses from task1
        # ! BUT you need to add the new clauses for task2

        mars_kb = FolKB(clauses)

        # --- Problem 1 Task 2.1: your code starts here---

        # --- Problem 1 Task 2.1: your code ends here---

        # --- Problem 1 Task 2.2-1: your code starts here---

        answer_fc = ?

        # --- Problem 1 Task 2.2-1: your code ends here---

        mars_kb = FolKB(clauses)

        # --- Problem 1 Task 2.2-2: your code starts here---

        # --- Problem 1 Task 2.2-2: your code ends here---

        # --- Problem 1 Task 2.2-2: your code starts here---

        answer_bc = ?

        # --- Problem 1 Task 2.2-3: your code ends here---

        return answer_fc, answer_bc

    def task3(self, clauses):
        # ! The `clauses` have included the clauses from task1 and task2
        # ! BUT you need to add the new clauses for task3

        mars_kb = FolKB(clauses)

        # --- Problem 1 Task 3-1: your code starts here---

        # --- Problem 1 Task 3-1: your code ends here---

        # --- Problem 1 Task 3-2: your code starts here---

        answer_fc = ?

        answer_bc = ?

        # --- Problem 1 Task 3-2: your code ends here---

        return answer_fc, answer_bc
