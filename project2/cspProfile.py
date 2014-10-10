import cProfile
from autograder import run_test

cProfile.run('run_test("test_cases/q6/sudoku1.test")',sort=True)