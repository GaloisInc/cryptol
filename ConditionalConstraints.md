# Conditional Constraints

## Syntax

The front-end AST has a new constructor:

```hs
data BindDef name = DPropGuards [([Prop name], Expr name)] | ...
```

which is parsed from the following syntax:

```
<name> : <signature>
<name> <pats>
[ | <props> => <expr> ]
```

## Expanding PropGuards

- Before renaming, a `Bind` with a `bDef = DPropGuards ...` will be expanded into several `Bind`s, one for each guard case. 
- The generated `Bind`s will have fresh names, but the names will have the same location as the original function's name.
- These generated `Bind`'s will have the same type as the original function, except that the list of type constraints will also include the `Prop name`s that appeared on the LHS of the originating ase of `DPropGuards`.
- The original function will have the `Expr name` in each of the `DPropGuards` cases replaced with a function call the appropriate, generated function.

## Renaming

The new constructor of `BindDef` is traversed as normal during renaming. This ensures that a function with `DPropGuards` ends up in the same mutual-recursion group as the generated functions that it calls.

## Typechecking

The back-end AST has a new constructor:

```hs
data Expr = EPropGuards [([Prop], Expr)] | ...
```

During typechecking, a `BindDef` of the form

```
DPropGuards [(props1, f1 x y), (prop2, f2 x y)]
```

is processed into a `Decl` of the form

```
Decl 
  { dDefinition =
      DExpr (EPropGuards
        [ (props1, f1 x y)
        , (props2, f2 x y) ])
  }
```

Each case of an `EPropGuards` is typechecked by first assuming the `props` and then typechecking the expression. However, this typechecking isn't really that important because by construction the expression is just a simple application that is ensured to be well-typed. But we can use this structure for more general purposes.