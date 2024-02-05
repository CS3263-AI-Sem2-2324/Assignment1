"""
Assignment 1 Problem 2 programming script.

* Group Member 1:
    - Name:
    - Student ID:

* Group Member 2:
    - Name:
    - Student ID:
"""

from typing import Callable
# !IMPORTANT: The following import is CORRECT for our evaluation, please DO NOT change it!
from FAIAss1CP.Agent import Agent, OnlineAgent, MCAgent
import random
import numpy as np


class MCT_Node:
    """Node in the Monte Carlo search tree, keeps track of the children states."""

    def __init__(self, parent=None, act=None, state=None, record=None, U=0, N=0):
        self.__dict__.update(parent=parent, state=state, U=U, N=N)
        self.children = {}
        self.record = record
        self.act = act


class hillclimbingAgent(Agent):
    def __init__(self, problem):
        super().__init__(problem)

    def searching(self, s, actions_available, result: Callable, v: Callable):
        '''The hill climbing algorithm
        args:
            ::s:: current state
            ::actions_available:: the action you can take at current state
            ::result:: Callable, predict the next state given the current state and action
            ::v:: Callable, value of the states.
        returns:
            ::a:: actions to take next, if stop, return None
        '''

        a = None

        '''---your codes start here---'''



        '''----your codes end here----'''

        return a


class LRTAstarAgent(OnlineAgent):
    def __init__(self, problem):
        super().__init__(problem)
        self.H = {}
        self.result = {}

    def search(self, s_previous, a_previous, s1, goal_test: Callable, h: Callable, actions: Callable, cost: Callable):
        '''The searching algorithm of Learning Real-time A*
        args:
            :s_previous: previous state
            :a_previous: previous action
            :s1: current state
            :goal_test: Callable, test whether a state is a goal
            :h: Callable, heuristic function
            :actions: Callable, return the available actions given the state
        returns:
            :a: next action to take
        '''

        a = None

        '''---your codes start here---'''



        '''----your codes end here----'''

        return a

    def cost(self, s, a, h: Callable, c: Callable):
        '''Returns cost to move from state 's' given the action 'a'.
        args:
            :s: current state (list)
            :a: current action (int)
            :h: heuristic function (callable)
            :c: cost function(callable)
        returns:
            :cost_value: the cost value to the next state (float)
        '''
        cost_value = None

        '''---your codes start here---'''



        '''----your codes end here----'''

        return cost_value


class MCTSAgent(MCAgent):
    def __init__(self, problem):
        super().__init__(problem)
        self.N = 20
        self.maze = problem.maze
        self.record = np.zeros((self.maze.width, self.maze.height))
        self.H = {}
        self.result = {}

    def ucb(self, n, C=1.4):
        ucb = np.inf if n.N == 0 else n.U / n.N + C * np.sqrt(np.log(n.parent.N) / n.N)
        return ucb

    def takeaction(self, act, record):
        new = record.copy()
        new[act[0]][act[1]] += 1
        return new

    def search(self, s, h: Callable, goal_test: Callable, actions: Callable, cost: Callable, is_terminal: Callable,
               result: Callable, utility: Callable):
        if goal_test(s):
            a = None
            return a

        record = self.record.copy()
        self.record[s[0]][s[1]] += 1
        root = MCT_Node(state=s, record=self.takeaction(s, record))

        for _ in range(self.N):
            '''---your codes start here---'''



            '''----your codes end here----'''

        max_state = max(root.children, key=lambda p: p.N)

        return max_state.act

    def select(self, n, actions: Callable):
        """select a leaf node in the tree"""
        if n.children:
            '''---your codes start here---'''



            '''----your codes end here----'''
        else:
            return n

    def expand(self, n, terminal_test: Callable, result: Callable, actions: Callable):
        """expand the leaf node by adding all its children states"""

        '''---your codes start here---'''



        '''----your codes end here----'''

        return self.select(n, actions)

    def simulate(self, child, actions: Callable, is_terminal: Callable, result: Callable, utility: Callable):
        """simulate the utility of current state by random picking a step"""
        cost = 1
        state = child.state
        record = child.record
        while not is_terminal(state, record):
            action = random.choice(list(actions(state, record)))
            state = result(state, action)
            record = self.takeaction(state, record)
            cost += 1
        v = utility(state, cost)
        return v

    def backprop(self, n, utility):
        """passing the utility back to all parent nodes"""
        if utility > 0:
            n.U += utility
        n.N += 1
        if n.parent:
            self.backprop(n.parent, utility)


agent_list = {
    'hill_climbing': hillclimbingAgent,
    'lrtastar': LRTAstarAgent,
    'MCTS': MCTSAgent,
}
