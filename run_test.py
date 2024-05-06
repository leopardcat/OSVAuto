import unittest
import importlib.util
import os

def execute_unit_tests(file_paths):
    suite = unittest.TestSuite()
    
    for file_path in file_paths:
        module_name = os.path.splitext(os.path.basename(file_path))[0]
        spec = importlib.util.spec_from_file_location(module_name, file_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        test_loader = unittest.TestLoader()
        test_suite = test_loader.loadTestsFromModule(module)
        suite.addTests(test_suite)
        
    runner = unittest.TextTestRunner()
    result = runner.run(suite)
    
    return result

file_list = [
    'osverify/tests/type_test.py',
    'osverify/tests/term_test.py',
    'osverify/tests/theory_test.py',
    'osverify/tests/match_test.py',
    'osverify/tests/simplify_test.py',
    'osverify/tests/tactic_test.py',
    'osverify/tests/z3wrapper_test.py',
    'osverify/tests/model_test.py'
]

test_result = execute_unit_tests(file_list)
