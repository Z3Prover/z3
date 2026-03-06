/**
Copyright (c) 2024 Microsoft Corporation
   
Module Name:

    PolymorphicDatatypeExample.java

Abstract:

    Example demonstrating the use of polymorphic (parametric) datatypes in Z3's Java API.
    This example creates a polymorphic List[T] datatype and demonstrates its usage.

Author:

    GitHub Copilot 2024-01-30

Notes:
    
**/

import com.microsoft.z3.*;

public class PolymorphicDatatypeExample {
    
    /**
     * Create a polymorphic List[T] datatype.
     * This is equivalent to:
     *   datatype List[T] = nil | cons(head: T, tail: List[T])
     */
    static void polymorphicListExample(Context ctx) {
        System.out.println("PolymorphicListExample");
        
        // Create a type variable T
        TypeVarSort T = ctx.mkTypeVariable("T");
        
        // Create constructors for the List[T] datatype
        // nil constructor (no arguments)
        Constructor<Object> nil = ctx.mkConstructor("nil", "is_nil", null, null, null);
        
        // cons constructor with head:T and tail:List[T]
        String[] fieldNames = new String[] { "head", "tail" };
        Sort[] fieldSorts = new Sort[] { T, null }; // null means recursive reference
        int[] sortRefs = new int[] { 0, 0 }; // both refer to the datatype being defined
        Constructor<Object> cons = ctx.mkConstructor("cons", "is_cons", fieldNames, fieldSorts, sortRefs);
        
        // Create the polymorphic List[T] datatype
        Constructor<Object>[] constructors = new Constructor[] { nil, cons };
        DatatypeSort<Object> listSort = ctx.mkPolymorphicDatatypeSort("List", new Sort[]{T}, constructors);
        
        System.out.println("Created polymorphic List datatype: " + listSort);
        
        // Get the constructor and accessor functions
        FuncDecl<?>[] listConstructors = listSort.getConstructors();
        FuncDecl<?> nilDecl = listConstructors[0];
        FuncDecl<?> consDecl = listConstructors[1];
        
        System.out.println("nil constructor: " + nilDecl);
        System.out.println("cons constructor: " + consDecl);
        
        // Get accessors
        FuncDecl<?>[][] accessors = listSort.getAccessors();
        if (accessors.length > 1 && accessors[1].length == 2) {
            FuncDecl<?> headAccessor = accessors[1][0];
            FuncDecl<?> tailAccessor = accessors[1][1];
            System.out.println("head accessor: " + headAccessor);
            System.out.println("tail accessor: " + tailAccessor);
        }
        
        System.out.println("Polymorphic List example completed successfully!");
    }
    
    /**
     * Create a polymorphic Option[T] datatype (like Maybe in Haskell).
     * This is equivalent to:
     *   datatype Option[T] = none | some(value: T)
     */
    static void polymorphicOptionExample(Context ctx) {
        System.out.println("\nPolymorphicOptionExample");
        
        // Create a type variable T
        TypeVarSort T = ctx.mkTypeVariable("T");
        
        // Create constructors for Option[T]
        Constructor<Object> none = ctx.mkConstructor("none", "is_none", null, null, null);
        
        String[] fieldNames = new String[] { "value" };
        Sort[] fieldSorts = new Sort[] { T };
        int[] sortRefs = new int[] { 0 }; // not used since T is not recursive
        Constructor<Object> some = ctx.mkConstructor("some", "is_some", fieldNames, fieldSorts, sortRefs);
        
        // Create the polymorphic Option[T] datatype
        Constructor<Object>[] constructors = new Constructor[] { none, some };
        DatatypeSort<Object> optionSort = ctx.mkPolymorphicDatatypeSort("Option", new Sort[]{T}, constructors);
        
        System.out.println("Created polymorphic Option datatype: " + optionSort);
        
        FuncDecl<?>[] optionConstructors = optionSort.getConstructors();
        System.out.println("none constructor: " + optionConstructors[0]);
        System.out.println("some constructor: " + optionConstructors[1]);
        
        System.out.println("Polymorphic Option example completed successfully!");
    }
    
    /**
     * Demonstrate type variables can be created with different names
     */
    static void typeVariableExample(Context ctx) {
        System.out.println("\nTypeVariableExample");
        
        TypeVarSort T = ctx.mkTypeVariable("T");
        TypeVarSort U = ctx.mkTypeVariable("U");
        TypeVarSort V = ctx.mkTypeVariable("V");
        
        System.out.println("Created type variable T: " + T);
        System.out.println("Created type variable U: " + U);
        System.out.println("Created type variable V: " + V);
        
        // Type variables can be used as sort parameters
        System.out.println("Type variables can be used as parameters for polymorphic datatypes");
    }

    public static void main(String[] args) {
        try {
            // Use try-with-resources to ensure proper cleanup
            try (Context ctx = new Context()) {
                typeVariableExample(ctx);
                polymorphicListExample(ctx);
                polymorphicOptionExample(ctx);
                
                System.out.println("\n=== All polymorphic datatype examples completed successfully! ===");
            }
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }
}
