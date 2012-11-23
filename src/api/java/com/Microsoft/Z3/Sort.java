/**
 * This file was automatically generated from Sort.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * The Sort class implements type information for ASTs.
     **/
    public class Sort extends AST
    {
        /**
         * Comparison operator.
         * <param name="a">A Sort</param>
         * <param name="b">A Sort</param>
         * @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
         * and represent the same sort; false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Comparison operator.
         * <param name="a">A Sort</param>
         * <param name="b">A Sort</param>
         * @return True if <paramref name="a"/> and <paramref name="b"/> are not from the same context 
         * or represent different sorts; false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Equality operator for objects of type Sort.
         * <param name="o"></param>
         * @return 
         **/
        public boolean Equals(object o)
        {
            Sort casted = o as Sort;
            if (casted == null) return false;
            return this == casted;
        }

        /**
         * Hash code generation for Sorts
         * @return A hash code
         **/
        public int GetHashCode()
        {
            return super.GetHashCode();
        }

        /**
         * Returns a unique identifier for the sort.
         **/
            public long Id()  { return Native.getSortId(Context.nCtx, NativeObject); }

        /**
         * The kind of the sort.
         **/
        public Z3_sort_kind SortKind()  { return (Z3_sort_kind)Native.getSortKind(Context.nCtx, NativeObject); }

        /**
         * The name of the sort
         **/
        public Symbol Name()  {
                
                return Symbol.Create(Context, Native.getSortName(Context.nCtx, NativeObject)); }
        }

        /**
         * A string representation of the sort.
         **/
        public String toString()
        {
            return Native.sorttoString(Context.nCtx, NativeObject);

        /**
         * Sort constructor
         **/
        protected Sort(Context ctx) { super(ctx);  }
        Sort(Context ctx, IntPtr obj) { super(ctx, obj);  }

        void CheckNativeObject(IntPtr obj)
        {
            if (Native.getAstKind(Context.nCtx, obj) != (long)Z3_ast_kind.Z3_SORT_AST)
                throw new Z3Exception("Underlying object is not a sort");
            super.CheckNativeObject(obj);
        }

        static Sort Create(Context ctx, IntPtr obj)
        {
            
            

            switch ((Z3_sort_kind)Native.getSortKind(ctx.nCtx, obj))
            {
                case Z3_sort_kind.Z3_ARRAY_SORT: return new ArraySort(ctx, obj);
                case Z3_sort_kind.Z3_BOOL_SORT: return new BoolSort(ctx, obj);
                case Z3_sort_kind.Z3_BV_SORT: return new BitVecSort(ctx, obj);
                case Z3_sort_kind.Z3_DATATYPE_SORT: return new DatatypeSort(ctx, obj);
                case Z3_sort_kind.Z3_INT_SORT: return new IntSort(ctx, obj);
                case Z3_sort_kind.Z3_REAL_SORT: return new RealSort(ctx, obj);
                case Z3_sort_kind.Z3_UNINTERPRETED_SORT: return new UninterpretedSort(ctx, obj);
                case Z3_sort_kind.Z3_FINITE_DOMAIN_SORT: return new FiniteDomainSort(ctx, obj);
                case Z3_sort_kind.Z3_RELATION_SORT: return new RelationSort(ctx, obj);
                default:
                    throw new Z3Exception("Unknown sort kind");
            }
        }
    }

    /**
     * A Boolean sort.
     **/
    public class BoolSort extends Sort
    {
        BoolSort(Context ctx, IntPtr obj) { super(ctx, obj);  }
        BoolSort(Context ctx) { super(ctx, Native.mkBooleanSort(ctx.nCtx));  }
    };

    /**
     * An arithmetic sort, i.e., Int or Real.
     **/
    public class ArithSort extends Sort
    {
        ArithSort(Context ctx, IntPtr obj) { super(ctx, obj);  }
    };

    /**
     *  An Integer sort
     **/
    public class IntSort extends ArithSort
    {
        IntSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        IntSort(Context ctx)
            { super(ctx, Native.mkIntSort(ctx.nCtx));
            
        }
    }

    /**
     * A real sort
     **/
    public class RealSort extends ArithSort
    {
        RealSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        RealSort(Context ctx)
            { super(ctx, Native.mkRealSort(ctx.nCtx));
            
        }
    }

    /**
     * Bit-vector sorts.
     **/
    public class BitVecSort extends Sort
    {
        /**
         * The size of the bit-vector sort.
         **/
        public long Size()  { return Native.getBvSortSize(Context.nCtx, NativeObject); }

        BitVecSort(Context ctx, IntPtr obj) { super(ctx, obj);  }
        BitVecSort(Context ctx, long size) { super(ctx, Native.mkBvSort(ctx.nCtx, size));  }
    };

    /**
     * Array sorts.
     **/
    public class ArraySort extends Sort
    {
        /**
         * The domain of the array sort.
         **/
        public Sort Domain()  {
                

                return Sort.Create(Context, Native.getArraySortDomain(Context.nCtx, NativeObject)); }
        }

        /**
         * The range of the array sort.
         **/
        public Sort Range()  {
                

                return Sort.Create(Context, Native.getArraySortRange(Context.nCtx, NativeObject)); }
        }

        ArraySort(Context ctx, IntPtr obj) { super(ctx, obj);  }
        ArraySort(Context ctx, Sort domain, Sort range)
            { super(ctx, Native.mkArraySort(ctx.nCtx, domain.NativeObject, range.NativeObject));
            
            
            
    };

    /**
     * Datatype sorts.
     **/
    public class DatatypeSort extends Sort
    {
        /**
         * The number of constructors of the datatype sort.
         **/
        public long NumConstructors()  { return Native.getDatatypeSortNumConstructors(Context.nCtx, NativeObject); }

        /**
         * The constructors.
         **/
        public FuncDecl[] Constructors() 
            {
                

                long n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (long i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getDatatypeSortConstructor(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The recognizers.
         **/
        public FuncDecl[] Recognizers() 
            {
                

                long n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (long i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getDatatypeSortRecognizer(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The constructor accessors.
         **/
        public FuncDecl[][] Accessors() 
            {
                

                long n = NumConstructors;
                FuncDecl[][] res = new FuncDecl[n][];
                for (long i = 0; i < n; i++)
                {
                    FuncDecl fd = new FuncDecl(Context, Native.getDatatypeSortConstructor(Context.nCtx, NativeObject, i));
                    long ds = fd.DomainSize;
                    FuncDecl[] tmp = new FuncDecl[ds];
                    for (long j = 0; j < ds; j++)
                        tmp[j] = new FuncDecl(Context, Native.getDatatypeSortConstructorAccessor(Context.nCtx, NativeObject, i, j));
                    res[i] = tmp;
                }
                return res;
        }

        DatatypeSort(Context ctx, IntPtr obj) { super(ctx, obj);  }

        DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
            { super(ctx, Native.mkDatatype(ctx.nCtx, name.NativeObject, (long)constructors.Length, ArrayToNative(constructors)));
            
            
            
        }
    };

    /**
     * Uninterpreted Sorts
     **/
    public class UninterpretedSort extends Sort
    {
        UninterpretedSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        UninterpretedSort(Context ctx, Symbol s)
            { super(ctx, Native.mkUninterpretedSort(ctx.nCtx, s.NativeObject));
            
            
        }
    }

    /**
     * Tuple sorts.
     **/
    public class TupleSort extends Sort
    {
        /**
         * The constructor function of the tuple.
         **/
        public FuncDecl MkDecl()  {
                

                return new FuncDecl(Context, Native.getTupleSortMkDecl(Context.nCtx, NativeObject)); }
        }

        /**
         * The number of fields in the tuple.
         **/
        public long NumFields()  { return Native.getTupleSortNumFields(Context.nCtx, NativeObject); }

        /**
         * The field declarations.
         **/
        public FuncDecl[] FieldDecls() 
            {
                

                long n = NumFields;
                FuncDecl[] res = new FuncDecl[n];
                for (long i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getTupleSortFieldDecl(Context.nCtx, NativeObject, i));
                return res;
            }

        TupleSort(Context ctx, Symbol name, long numFields, Symbol[] fieldNames, Sort[] fieldSorts)
            { super(ctx);
            
            

            IntPtr t = IntPtr.Zero;
            NativeObject = Native.mkTupleSort(ctx.nCtx, name.NativeObject, numFields,
                                                   Symbol.ArrayToNative(fieldNames), AST.ArrayToNative(fieldSorts),
                                                   t, new IntPtr[numFields]);
        }
    };

    /**
     * Enumeration sorts.
     **/
    public class EnumSort extends Sort
    {
        /**
         * The function declarations of the constants in the enumeration.
         **/
        public FuncDecl[] ConstDecls()  {
                

                return _constdecls; }
        }

        /**
         * The constants in the enumeration.
         **/
        public Expr[] Consts()  {
                

                return _consts; }
        }

        /**
         * The test predicates for the constants in the enumeration.
         **/
        public FuncDecl[] TesterDecls()  {
                
                
                return _testerdecls;
            }


        private void ObjectInvariant()
        {
            
            
            
        }

        

        private FuncDecl[] _constdecls = null, _testerdecls = null;
        private Expr[] _consts = null;

        EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
            { super(ctx);
            
            
            

            int n = enumNames.Length;
            IntPtr[] n_constdecls = new IntPtr[n];
            IntPtr[] n_testers = new IntPtr[n];
            NativeObject = Native.mkEnumerationSort(ctx.nCtx, name.NativeObject, (long)n,
                                                         Symbol.ArrayToNative(enumNames), n_constdecls, n_testers);
            _constdecls = new FuncDecl[n];            
            for (long i = 0; i < n; i++)            
                _constdecls[i] = new FuncDecl(ctx, n_constdecls[i]);
            _testerdecls = new FuncDecl[n];
            for (long i = 0; i < n; i++)
                _testerdecls[i] = new FuncDecl(ctx, n_testers[i]);
            _consts = new Expr[n];
            for (long i = 0; i < n; i++)
                _consts[i] = ctx.MkApp(_constdecls[i]);
        }
    };

    /**
     * List sorts.
     **/
    public class ListSort extends Sort
    {
        /**
         * The declaration of the nil function of this list sort.
         **/
        public FuncDecl NilDecl() 
            
            return nilDecl; } }

        /**
         * The empty list.
         **/
        public Expr Nil() 
            {
                
                return nilConst;
            }

        /**
         * The declaration of the isNil function of this list sort.
         **/
        public FuncDecl IsNilDecl() 
            {
                
                return isNilDecl;
            }

        /**
         * The declaration of the cons function of this list sort.
         **/
        public FuncDecl ConsDecl() 
            {
                
                return consDecl;
            }

        /**
         * The declaration of the isCons function of this list sort.
         * 
         **/
        public FuncDecl IsConsDecl() 
            {
                
                return isConsDecl;
            }

        /**
         * The declaration of the head function of this list sort.
         **/
        public FuncDecl HeadDecl() 
            {
                
                return headDecl;
            }

        /**
         * The declaration of the tail function of this list sort.
         **/
        public FuncDecl TailDecl() 
            {
                
                return tailDecl;
            }


        private void ObjectInvariant()
        {
            
            
            
            
            
            
            
        }

        

        private FuncDecl nilDecl, isNilDecl, consDecl, isConsDecl, headDecl, tailDecl;
        private Expr nilConst;

        ListSort(Context ctx, Symbol name, Sort elemSort)
            { super(ctx);
            
            
            

            IntPtr inil = IntPtr.Zero,
                   iisnil = IntPtr.Zero,
                   icons = IntPtr.Zero,
                   iiscons = IntPtr.Zero,
                   ihead = IntPtr.Zero,
                   itail = IntPtr.Zero;

            NativeObject = Native.mkListSort(ctx.nCtx, name.NativeObject, elemSort.NativeObject,
                                                  inil, iisnil, icons, iiscons, ihead, itail);
            nilDecl = new FuncDecl(ctx, inil);
            isNilDecl = new FuncDecl(ctx, iisnil);
            consDecl = new FuncDecl(ctx, icons);
            isConsDecl = new FuncDecl(ctx, iiscons);
            headDecl = new FuncDecl(ctx, ihead);
            tailDecl = new FuncDecl(ctx, itail);
            nilConst = ctx.MkConst(nilDecl);
        }
    };

    /**
     * Relation sorts.
     **/
    public class RelationSort extends Sort
    {
        /**
         * The arity of the relation sort.
         **/
        public long Arity()  { return Native.getRelationArity(Context.nCtx, NativeObject); }

        /**
         * The sorts of the columns of the relation sort.
         **/
        public Sort[] ColumnSorts() 
            {
                

                if (m_columnSorts != null)
                    return m_columnSorts;

                long n = Arity;
                Sort[] res = new Sort[n];
                for (long i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.getRelationColumn(Context.nCtx, NativeObject, i));
                return res;
            }

        private Sort[] m_columnSorts = null;

        RelationSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }        
    }

    /**
     * Finite domain sorts.
     **/
    public class FiniteDomainSort extends Sort
    {
        /**
         * The size of the finite domain sort.
         **/
        public ulong Size()  { ulong res = 0; Native.getFiniteDomainSortSize(Context.nCtx, NativeObject, ref res); return res; }

        FiniteDomainSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        FiniteDomainSort(Context ctx, Symbol name, ulong size)
            { super(ctx, Native.mkFiniteDomainSort(ctx.nCtx, name.NativeObject, size));
            
            

        }
    }

    /**
     * Set sorts.
     **/
    public class SetSort extends Sort
    {
        SetSort(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        SetSort(Context ctx, Sort ty)
            { super(ctx, Native.mkSetSort(ctx.nCtx, ty.NativeObject));
            
            
        }
    }
