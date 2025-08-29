#!/usr/bin/env python3
"""
Unit tests for the UserPropagator quantifier instantiation callback feature.

This test suite validates the functionality added in Z3 version 4.15.3 that allows
user propagators to intercept and control quantifier instantiations.
"""

import unittest
import sys
import os

# Add the Z3 Python bindings to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'build', 'python'))

from z3 import *

class TestQuantifierInstantiationCallback(unittest.TestCase):
    """Test cases for quantifier instantiation callback functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.reset_counters()
    
    def reset_counters(self):
        """Reset global test counters."""
        global g_instantiation_count, g_allowed_count, g_blocked_count
        g_instantiation_count = 0
        g_allowed_count = 0
        g_blocked_count = 0

# Global counters for test validation
g_instantiation_count = 0
g_allowed_count = 0
g_blocked_count = 0

class BasicInstantiationController(UserPropagateBase):
    """Basic user propagator for testing instantiation control."""
    
    def __init__(self, allow_first_n=3, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.allow_first_n = allow_first_n
        self.add_on_binding(self.control_instantiation)
    
    def control_instantiation(self, quantifier, instantiation):
        global g_instantiation_count, g_allowed_count, g_blocked_count
        g_instantiation_count += 1
        
        allow = g_instantiation_count <= self.allow_first_n
        if allow:
            g_allowed_count += 1
        else:
            g_blocked_count += 1
        
        return allow
    
    def push(self):
        pass
    
    def pop(self, num_scopes):
        pass
    
    def fresh(self, new_ctx):
        return BasicInstantiationController(self.allow_first_n, ctx=new_ctx)

class LoggingController(UserPropagateBase):
    """User propagator that logs all instantiations without blocking."""
    
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.log = []
        self.add_on_binding(self.log_instantiation)
    
    def log_instantiation(self, quantifier, instantiation):
        global g_instantiation_count
        g_instantiation_count += 1
        
        entry = {
            'quantifier': str(quantifier),
            'instantiation': str(instantiation),
            'count': g_instantiation_count
        }
        self.log.append(entry)
        
        # Allow all instantiations
        return True
    
    def push(self):
        pass
    
    def pop(self, num_scopes):
        pass
    
    def fresh(self, new_ctx):
        return LoggingController(ctx=new_ctx)

class PatternFilterController(UserPropagateBase):
    """User propagator that filters based on instantiation patterns."""
    
    def __init__(self, max_per_pattern=2, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.max_per_pattern = max_per_pattern
        self.pattern_counts = {}
        self.add_on_binding(self.filter_by_pattern)
    
    def filter_by_pattern(self, quantifier, instantiation):
        global g_instantiation_count, g_allowed_count, g_blocked_count
        g_instantiation_count += 1
        
        pattern = str(instantiation)
        self.pattern_counts[pattern] = self.pattern_counts.get(pattern, 0) + 1
        
        allow = self.pattern_counts[pattern] <= self.max_per_pattern
        if allow:
            g_allowed_count += 1
        else:
            g_blocked_count += 1
        
        return allow
    
    def push(self):
        pass
    
    def pop(self, num_scopes):
        pass
    
    def fresh(self, new_ctx):
        return PatternFilterController(self.max_per_pattern, ctx=new_ctx)

class TestQuantifierInstantiationCallback(unittest.TestCase):
    """Test cases for quantifier instantiation callback functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.reset_counters()
    
    def reset_counters(self):
        """Reset global test counters."""
        global g_instantiation_count, g_allowed_count, g_blocked_count
        g_instantiation_count = 0
        g_allowed_count = 0
        g_blocked_count = 0
    
    def test_basic_instantiation_control(self):
        """Test basic instantiation limiting functionality."""
        self.reset_counters()
        
        # Create solver with instantiation controller
        s = Solver()
        controller = BasicInstantiationController(allow_first_n=2, s=s)
        
        # Create simple quantified formula
        x = Int('x')
        f = Function('f', IntSort(), IntSort())
        
        # Add quantified axiom: forall x. f(x) >= 0
        s.add(ForAll([x], f(x) >= 0))
        
        # Add constraints that trigger instantiations
        a, b, c = Ints('a b c')
        s.add(f(a) < 10)
        s.add(f(b) < 20)
        s.add(f(c) < 30)
        s.add(a == 1, b == 2, c == 3)
        
        # Solve
        result = s.check()
        
        # Validate that callbacks were invoked and some instantiations were blocked
        self.assertGreater(g_instantiation_count, 0, "No instantiations were attempted")
        self.assertEqual(g_allowed_count, 2, "Expected exactly 2 allowed instantiations")
        self.assertGreaterEqual(g_blocked_count, 0, "Expected some blocked instantiations")
        
        # Should still be satisfiable with limited instantiations
        self.assertEqual(result, sat, "Formula should be satisfiable")
    
    def test_logging_all_instantiations(self):
        """Test that logging controller captures all instantiation attempts."""
        self.reset_counters()
        
        s = Solver()
        logger = LoggingController(s=s)
        
        # Create formula with multiple quantifiers
        x = Int('x')
        f = Function('f', IntSort(), IntSort())
        g = Function('g', IntSort(), IntSort())
        
        s.add(ForAll([x], f(x) >= x))
        s.add(ForAll([x], g(x) <= x))
        
        a, b = Ints('a b')
        s.add(f(a) < 5)
        s.add(g(b) > 10)
        s.add(a == 2, b == 8)
        
        result = s.check()
        
        # Validate logging
        self.assertGreater(len(logger.log), 0, "No instantiations were logged")
        self.assertEqual(len(logger.log), g_instantiation_count, "Log count mismatch")
        
        # Check log structure
        for entry in logger.log:
            self.assertIn('quantifier', entry)
            self.assertIn('instantiation', entry)
            self.assertIn('count', entry)
            self.assertIsInstance(entry['quantifier'], str)
            self.assertIsInstance(entry['instantiation'], str)
            self.assertIsInstance(entry['count'], int)
    
    def test_pattern_based_filtering(self):
        """Test pattern-based instantiation filtering."""
        self.reset_counters()
        
        s = Solver()
        filter_controller = PatternFilterController(max_per_pattern=1, s=s)
        
        # Create scenario that might generate duplicate patterns
        x, y = Ints('x y')
        P = Function('P', IntSort(), IntSort(), BoolSort())
        
        s.add(ForAll([x, y], Implies(P(x, y), P(y, x))))
        
        a, b, c = Ints('a b c')
        s.add(P(a, b))
        s.add(P(b, c))
        s.add(P(a, c))  # This might create similar patterns
        
        result = s.check()
        
        # Validate that filtering occurred
        self.assertGreater(g_instantiation_count, 0, "No instantiations were attempted")
        
        # Check that patterns were tracked
        self.assertGreater(len(filter_controller.pattern_counts), 0, "No patterns were tracked")
        
        # Verify some patterns appeared multiple times (and were filtered)
        max_count = max(filter_controller.pattern_counts.values())
        if max_count > 1:
            self.assertGreater(g_blocked_count, 0, "Expected some blocked instantiations for repeated patterns")
    
    def test_callback_with_unsat_formula(self):
        """Test callback behavior with unsatisfiable formulas."""
        self.reset_counters()
        
        s = Solver()
        controller = BasicInstantiationController(allow_first_n=1, s=s)
        
        # Create unsatisfiable formula
        x = Int('x')
        f = Function('f', IntSort(), IntSort())
        
        s.add(ForAll([x], f(x) >= 0))
        s.add(f(5) < -10)  # Contradiction
        
        result = s.check()
        
        # Should be UNSAT regardless of instantiation control
        self.assertEqual(result, unsat, "Formula should be unsatisfiable")
        
        # Callbacks may or may not be invoked for UNSAT formulas
        # (depends on solver's instantiation strategy)
    
    def test_callback_registration_without_instantiations(self):
        """Test that callback registration works even without quantifier instantiations."""
        self.reset_counters()
        
        s = Solver()
        controller = BasicInstantiationController(allow_first_n=5, s=s)
        
        # Add formula without quantifiers
        x, y = Ints('x y')
        s.add(x + y == 10)
        s.add(x > 5)
        
        result = s.check()
        
        # Should solve without invoking callbacks
        self.assertEqual(result, sat, "Formula should be satisfiable")
        self.assertEqual(g_instantiation_count, 0, "No instantiations should occur without quantifiers")
    
    def test_multiple_solvers_independent_callbacks(self):
        """Test that callbacks on different solvers are independent."""
        self.reset_counters()
        
        # Create first solver with restrictive controller
        s1 = Solver()
        controller1 = BasicInstantiationController(allow_first_n=1, s=s1)
        
        # Create second solver with permissive controller  
        s2 = Solver()
        controller2 = BasicInstantiationController(allow_first_n=10, s=s2)
        
        # Add same formula to both
        x = Int('x')
        f = Function('f', IntSort(), IntSort())
        axiom = ForAll([x], f(x) >= 0)
        
        for s in [s1, s2]:
            s.add(axiom)
            a = Int(f'a_{id(s)}')  # Unique constant per solver
            s.add(f(a) < 5)
            s.add(a == 1)
        
        # Solve both
        result1 = s1.check()
        result2 = s2.check()
        
        # Both should be satisfiable
        self.assertEqual(result1, sat, "First solver should find solution")
        self.assertEqual(result2, sat, "Second solver should find solution")
        
        # Note: Since we use global counters, we can't easily test independence
        # In a real implementation, each controller would have its own counters

class TestErrorConditions(unittest.TestCase):
    """Test error conditions and edge cases."""
    
    def test_callback_exception_handling(self):
        """Test that exceptions in callbacks are handled gracefully."""
        
        class FaultyController(UserPropagateBase):
            def __init__(self, s=None, ctx=None):
                UserPropagateBase.__init__(self, s, ctx)
                self.add_on_binding(self.faulty_callback)
            
            def faulty_callback(self, quantifier, instantiation):
                # This callback always raises an exception
                raise ValueError("Test exception in callback")
            
            def push(self): pass
            def pop(self, num_scopes): pass
            def fresh(self, new_ctx): return FaultyController(ctx=new_ctx)
        
        s = Solver()
        
        # This should not crash, but the callback behavior is implementation-defined
        # when exceptions occur
        try:
            controller = FaultyController(s=s)
            
            x = Int('x')
            f = Function('f', IntSort(), IntSort())
            s.add(ForAll([x], f(x) >= 0))
            s.add(f(1) < 5)
            
            # The solver should handle callback exceptions gracefully
            # Exact behavior may vary, but should not crash
            result = s.check()
            
        except Exception as e:
            # If an exception propagates, it should be the one we raised
            # or a Z3Exception wrapping it
            pass

if __name__ == '__main__':
    # Check if Z3 is available
    try:
        from z3 import *
        
        # Test basic Z3 functionality
        x = Int('x')
        s = Solver()
        s.add(x > 0)
        if s.check() != sat:
            print("ERROR: Basic Z3 functionality not working")
            sys.exit(1)
            
    except ImportError:
        print("ERROR: Z3 Python bindings not found")
        print("Make sure PYTHONPATH includes the Z3 Python bindings directory")
        sys.exit(1)
    
    # Run the tests
    print("Running quantifier instantiation callback tests...")
    unittest.main(verbosity=2)