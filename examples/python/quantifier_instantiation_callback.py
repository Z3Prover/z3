#!/usr/bin/env python3
"""
Example demonstrating the UserPropagator callback for quantifier instantiations in Z3.

This feature was added in Z3 version 4.15.3 and allows user propagators to intercept
and control quantifier instantiations. The callback receives the quantifier and its
proposed instantiation, and can return False to discard the instantiation.

This provides fine-grained control over the quantifier instantiation process,
allowing users to:
1. Inspect and log instantiations
2. Filter out undesired instantiations
3. Implement custom instantiation strategies
4. Delay certain instantiations for performance reasons
"""

from z3 import *

class QuantifierInstantiationController(UserPropagateBase):
    """
    A user propagator that controls quantifier instantiations.
    
    This example demonstrates how to:
    1. Register a quantifier instantiation callback
    2. Inspect proposed instantiations
    3. Selectively allow or discard instantiations
    """
    
    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.instantiation_count = 0
        self.allowed_instantiations = 0
        self.blocked_instantiations = 0
        self.instantiation_log = []
        
        # Register the quantifier instantiation callback
        self.add_on_binding(self.on_quantifier_instantiation)
    
    def on_quantifier_instantiation(self, quantifier, instantiation):
        """
        Callback invoked when Z3 wants to instantiate a quantifier.
        
        Args:
            quantifier: The quantifier being instantiated (Z3 AST)
            instantiation: The proposed instantiation (Z3 AST)
            
        Returns:
            bool: True to allow the instantiation, False to discard it
        """
        self.instantiation_count += 1
        
        # Log the instantiation for inspection
        q_str = str(quantifier)
        inst_str = str(instantiation)
        self.instantiation_log.append((q_str, inst_str))
        
        print(f"Instantiation #{self.instantiation_count}:")
        print(f"  Quantifier: {q_str}")
        print(f"  Instantiation: {inst_str}")
        
        # Example filtering logic: allow only the first 3 instantiations
        # In practice, you might filter based on the structure of the instantiation,
        # performance considerations, or other criteria
        allow = self.instantiation_count <= 3
        
        if allow:
            self.allowed_instantiations += 1
            print(f"  -> ALLOWED (#{self.allowed_instantiations})")
        else:
            self.blocked_instantiations += 1
            print(f"  -> BLOCKED (#{self.blocked_instantiations})")
        
        print()
        return allow
    
    def push(self):
        # Required method for user propagators
        pass
    
    def pop(self, num_scopes):
        # Required method for user propagators  
        pass
    
    def fresh(self, new_ctx):
        # Required method for user propagators
        return QuantifierInstantiationController(ctx=new_ctx)
    
    def get_statistics(self):
        """Return statistics about instantiation control."""
        return {
            'total_instantiation_attempts': self.instantiation_count,
            'allowed_instantiations': self.allowed_instantiations,
            'blocked_instantiations': self.blocked_instantiations,
            'instantiation_log': self.instantiation_log
        }


def example_basic_quantifier_control():
    """
    Basic example showing how to control quantifier instantiations.
    """
    print("=" * 60)
    print("BASIC QUANTIFIER INSTANTIATION CONTROL EXAMPLE")
    print("=" * 60)
    
    # Create solver with user propagator
    s = Solver()
    controller = QuantifierInstantiationController(s)
    
    # Create a simple quantified formula
    x = Int('x')
    f = Function('f', IntSort(), IntSort())
    
    # Add a quantified axiom: forall x. f(x) >= 0
    axiom = ForAll([x], f(x) >= 0)
    s.add(axiom)
    
    # Add constraints that might trigger instantiations
    a, b, c = Ints('a b c')
    s.add(f(a) < 10)
    s.add(f(b) < 20) 
    s.add(f(c) < 30)
    
    # Also add constraints that should conflict if all instantiations are allowed
    s.add(a == 1)
    s.add(b == 2) 
    s.add(c == 3)
    
    print("Checking satisfiability with instantiation control...")
    result = s.check()
    print(f"Result: {result}")
    
    if result == sat:
        print(f"Model: {s.model()}")
    
    # Print statistics
    stats = controller.get_statistics()
    print(f"\nInstantiation Statistics:")
    print(f"  Total attempts: {stats['total_instantiation_attempts']}")
    print(f"  Allowed: {stats['allowed_instantiations']}")
    print(f"  Blocked: {stats['blocked_instantiations']}")


def example_advanced_filtering():
    """
    Advanced example showing more sophisticated instantiation filtering.
    """
    print("\n" + "=" * 60)
    print("ADVANCED INSTANTIATION FILTERING EXAMPLE")
    print("=" * 60)
    
    class AdvancedController(UserPropagateBase):
        def __init__(self, s=None, ctx=None):
            UserPropagateBase.__init__(self, s, ctx)
            self.instantiations_by_term = {}
            self.add_on_binding(self.smart_filter)
        
        def smart_filter(self, quantifier, instantiation):
            """
            Smart filtering based on instantiation content.
            """
            # Extract information about the instantiation
            q_str = str(quantifier)
            inst_str = str(instantiation)
            
            # Count instantiations per term pattern
            if inst_str not in self.instantiations_by_term:
                self.instantiations_by_term[inst_str] = 0
            self.instantiations_by_term[inst_str] += 1
            
            # Allow only up to 2 instantiations of the same pattern
            allow = self.instantiations_by_term[inst_str] <= 2
            
            print(f"Instantiation: {inst_str} (attempt #{self.instantiations_by_term[inst_str]})")
            print(f"  -> {'ALLOWED' if allow else 'BLOCKED'}")
            
            return allow
        
        def push(self):
            pass
        
        def pop(self, num_scopes):
            pass
        
        def fresh(self, new_ctx):
            return AdvancedController(ctx=new_ctx)
    
    # Create solver with advanced controller
    s = Solver()
    controller = AdvancedController(s)
    
    # Create a more complex scenario
    x, y = Ints('x y')
    P = Function('P', IntSort(), IntSort(), BoolSort())
    
    # Add quantified formula: forall x, y. P(x, y) => P(y, x)
    axiom = ForAll([x, y], Implies(P(x, y), P(y, x)))
    s.add(axiom)
    
    # Add facts that will trigger instantiations
    a, b, c = Ints('a b c')
    s.add(P(a, b))
    s.add(P(b, c))
    s.add(P(c, a))
    
    print("Checking satisfiability with advanced filtering...")
    result = s.check()
    print(f"Result: {result}")
    
    if result == sat:
        print(f"Model: {s.model()}")


def example_instantiation_logging():
    """
    Example focused on logging and analyzing instantiation patterns.
    """
    print("\n" + "=" * 60)
    print("INSTANTIATION LOGGING AND ANALYSIS EXAMPLE")  
    print("=" * 60)
    
    class LoggingController(UserPropagateBase):
        def __init__(self, s=None, ctx=None):
            UserPropagateBase.__init__(self, s, ctx)
            self.log = []
            self.add_on_binding(self.log_instantiation)
        
        def log_instantiation(self, quantifier, instantiation):
            """
            Log all instantiation attempts for later analysis.
            """
            entry = {
                'quantifier': str(quantifier),
                'instantiation': str(instantiation),
                'timestamp': len(self.log)
            }
            self.log.append(entry)
            
            # For this example, allow all instantiations
            return True
        
        def push(self):
            pass
        
        def pop(self, num_scopes):
            pass
        
        def fresh(self, new_ctx):
            return LoggingController(ctx=new_ctx)
        
        def analyze_patterns(self):
            """Analyze logged instantiation patterns."""
            print(f"Total instantiations logged: {len(self.log)}")
            
            # Group by quantifier
            by_quantifier = {}
            for entry in self.log:
                q = entry['quantifier']
                if q not in by_quantifier:
                    by_quantifier[q] = []
                by_quantifier[q].append(entry['instantiation'])
            
            for q, instantiations in by_quantifier.items():
                print(f"\nQuantifier: {q}")
                print(f"  Instantiations ({len(instantiations)}):")
                for i, inst in enumerate(instantiations, 1):
                    print(f"    {i}. {inst}")
    
    # Create solver with logging controller
    s = Solver()
    controller = LoggingController(s)
    
    # Create scenario with multiple quantifiers
    x = Int('x')
    f = Function('f', IntSort(), IntSort())
    g = Function('g', IntSort(), IntSort())
    
    # Add multiple quantified axioms
    s.add(ForAll([x], f(x) >= x))  # f(x) is at least x
    s.add(ForAll([x], g(x) <= x))  # g(x) is at most x
    
    # Add constraints to trigger instantiations
    a, b = Ints('a b')
    s.add(f(a) < 5)
    s.add(g(b) > 10)
    s.add(a == 2)
    s.add(b == 8)
    
    print("Solving with full logging enabled...")
    result = s.check()
    print(f"Result: {result}")
    
    # Analyze the logged instantiation patterns
    print("\nInstantiation Analysis:")
    controller.analyze_patterns()


if __name__ == "__main__":
    # Run all examples
    example_basic_quantifier_control()
    example_advanced_filtering()
    example_instantiation_logging()
    
    print("\n" + "=" * 60)
    print("All examples completed successfully!")
    print("=" * 60)