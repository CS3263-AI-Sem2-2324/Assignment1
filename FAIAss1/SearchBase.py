"""
Script for searching problems.
"""


class Problem:
    """The abstract class for a formal problem."""

    def __init__(self, initial, goal):
        """The constructor specifies the initial state, and a goal state."""
        self.initial = initial
        self.goal = goal

    def actions(self, state):
        """Return the actions that can be executed in the given state."""
        raise NotImplementedError

    def result(self, state, action):
        """Return the state that results from executing the given action in the given state."""
        raise NotImplementedError

    def goal_test(self, state):
        """Return True if the state is a goal."""
        return state == self.goal

    def path_cost(self, c, state1, action, state2):
        """Return the cost of a solution path that arrives at state2 from state1 via action,
        assuming cost c to get up to state1."""
        return c + 1

    def value(self, state):
        """Return a value for the given state."""
        raise NotImplementedError

    def is_terminal(self, state):
        """Return True if this is a final state for the game."""
        return not self.actions(state)

    def utility(self, state, player):
        """Return the value of this final state to player."""
        raise NotImplementedError
