"""
The script to config maze environments.
"""

walls_maze1 = [[(0, 1), (0, 2)],
               [(0, 1), (1, 1)],
               [(1, 1), (2, 1)],
               [(2, 1), (2, 2)]]

walls_maze2 = [[(0, 1), (1, 1)],
               [(1, 0), (1, 1)],
               [(1, 1), (2, 1)],
               [(1, 2), (2, 2)]]

walls_maze3 = [[(0, 0), (1, 0)],
               [(0, 1), (1, 1)],
               [(2, 1), (3, 1)],
               [(2, 2), (3, 2)]]

sizes = [(3, 3), (3, 3), (4, 3)]
goals = [[2, 2], [2, 2], [3, 2]]

walls = [walls_maze1, walls_maze2, walls_maze3]

action_name = ["UP", "DOWN", "LEFT", "RIGHT"]
