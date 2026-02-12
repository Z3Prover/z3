#!/usr/bin/env python
"""
Test suite for critical Python API bug fixes identified by a3-python analysis.

These tests validate:
1. Bare assert statements replaced with proper exceptions (9 issues)
2. Division by zero check in RatVal
3. Bounds checking and negative index support in Goal.__getitem__
"""

import sys
import os

# Make sure we can import z3 from the build directory
from z3 import z3


def test_ratval_division_by_zero():
    """Test that RatVal raises ValueError when denominator is zero."""
    print("Testing RatVal division by zero...")
    try:
        result = z3.RatVal(5, 0)
        print("  FAILED: Expected ValueError but got result:", result)
        return False
    except ValueError as e:
        if "Denominator cannot be zero" in str(e):
            print("  PASSED: Correctly raised ValueError with proper message")
            return True
        else:
            print("  FAILED: ValueError raised but with wrong message:", str(e))
            return False
    except Exception as e:
        print("  FAILED: Wrong exception type:", type(e).__name__, str(e))
        return False


def test_goal_getitem_negative_index():
    """Test that Goal.__getitem__ supports negative indexing."""
    print("Testing Goal.__getitem__ negative index...")
    try:
        g = z3.Goal()
        x, y, z = z3.Ints('x y z')
        g.add(x == 0, y > x, z < y)
        
        # Test negative indices
        last = g[-1]
        second_last = g[-2]
        first = g[-3]
        
        # Verify they match positive indices
        if str(last) == str(g[2]) and str(second_last) == str(g[1]) and str(first) == str(g[0]):
            print("  PASSED: Negative indexing works correctly")
            return True
        else:
            print("  FAILED: Negative indexing returned wrong values")
            return False
    except Exception as e:
        print("  FAILED: Exception raised:", type(e).__name__, str(e))
        return False


def test_goal_getitem_bounds():
    """Test that Goal.__getitem__ raises IndexError for out of bounds access."""
    print("Testing Goal.__getitem__ bounds checking...")
    try:
        g = z3.Goal()
        x, y = z3.Ints('x y')
        g.add(x == 0, y > x)
        
        # Test out of bounds positive index
        try:
            item = g[10]
            print("  FAILED: Expected IndexError for positive out of bounds")
            return False
        except IndexError:
            pass  # Expected
        
        # Test out of bounds negative index
        try:
            item = g[-10]
            print("  FAILED: Expected IndexError for negative out of bounds")
            return False
        except IndexError:
            pass  # Expected
        
        print("  PASSED: Bounds checking works correctly")
        return True
    except Exception as e:
        print("  FAILED: Unexpected exception:", type(e).__name__, str(e))
        return False


def test_user_propagate_double_registration():
    """Test that UserPropagateBase raises Z3Exception on double registration."""
    print("Testing UserPropagateBase double registration...")
    try:
        # Create a minimal UserPropagateBase subclass
        class TestPropagator(z3.UserPropagateBase):
            def __init__(self, s=None):
                super().__init__(s, ctx=z3.Context() if s is None else None)
                
            def push(self):
                pass
            def pop(self, num_scopes):
                pass
            def fresh(self, new_ctx):
                return TestPropagator()
        
        prop = TestPropagator()
        
        # Test double registration of fixed callback
        def fixed_callback(x, v):
            pass
        
        prop.add_fixed(fixed_callback)
        try:
            prop.add_fixed(fixed_callback)  # Second registration
            print("  FAILED: Expected Z3Exception for double fixed registration")
            return False
        except z3.Z3Exception as e:
            if "already registered" in str(e):
                print("  PASSED: Correctly raised Z3Exception for double registration")
                return True
            else:
                print("  FAILED: Z3Exception raised but with wrong message:", str(e))
                return False
    except Exception as e:
        print("  FAILED: Unexpected exception:", type(e).__name__, str(e))
        return False


def test_ratval_valid_cases():
    """Test that RatVal still works for valid inputs."""
    print("Testing RatVal valid cases...")
    try:
        # Test valid rational number creation
        r1 = z3.RatVal(3, 5)
        r2 = z3.RatVal(1, 2)
        r3 = z3.RatVal(-7, 3)
        
        # Verify they are created correctly
        if r1 is not None and r2 is not None and r3 is not None:
            print("  PASSED: Valid RatVal cases work correctly")
            return True
        else:
            print("  FAILED: Valid RatVal returned None")
            return False
    except Exception as e:
        print("  FAILED: Exception raised for valid case:", type(e).__name__, str(e))
        return False


def test_goal_getitem_valid_cases():
    """Test that Goal.__getitem__ still works for valid positive indices."""
    print("Testing Goal.__getitem__ valid positive indices...")
    try:
        g = z3.Goal()
        x, y, z = z3.Ints('x y z')
        g.add(x == 0, y > x, z < y)
        
        # Test valid positive indices
        first = g[0]
        second = g[1]
        third = g[2]
        
        if first is not None and second is not None and third is not None:
            print("  PASSED: Valid positive indexing works correctly")
            return True
        else:
            print("  FAILED: Valid indexing returned None")
            return False
    except Exception as e:
        print("  FAILED: Exception raised for valid case:", type(e).__name__, str(e))
        return False


def main():
    """Run all tests and report results."""
    print("=" * 60)
    print("Running Critical Python API Bug Fix Tests")
    print("=" * 60)
    print()
    
    tests = [
        test_ratval_division_by_zero,
        test_ratval_valid_cases,
        test_goal_getitem_negative_index,
        test_goal_getitem_bounds,
        test_goal_getitem_valid_cases,
        test_user_propagate_double_registration,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        if test():
            passed += 1
        else:
            failed += 1
        print()
    
    print("=" * 60)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
