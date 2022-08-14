LoadPackage("SmallSemi");

Read("lib/aut.g");

database_path:="data";

twist_matrix := function(obj, f)
  local i,j,m,n;
  n := Size(obj);
  m := NullMat(n,n);
  for i in [1..n] do
    for j in [1..n] do
      if obj[i^Inverse(f)][j^Inverse(f)] <> 0 then
        m[i][j] := obj[i^Inverse(f)][j^Inverse(f)]^f;
      fi;
    od;
  od;
  return m;
end;

is_fixed := function(f, n, k)
  local m;
  m := RecoverMultiplicationTable(n,k);
  if twist_matrix(m, f) = m then
    return true;
  else
    return false;
  fi;
end;

fix := function(n,k)
  return Group(Filtered(automorphism_group(n,k), x->is_fixed(x, n, k)));
end;

is_symmetric := function(n,k)
  local sg, m, f;

  m := RecoverMultiplicationTable(n,k);
  if m = TransposedMat(m) then
    return true;
  fi;
  sg := SemigroupByMultiplicationTableNC(TransposedMat(m));
  f := EquivalenceSmallSemigroup(sg);
  return IsSemigroupHomomorphism(f);
end;

number_of_semigroups := function(n)
  local k, sym, non;
  sym := 0;
  non := 0;
  for k in [1..NrSmallSemigroups(n)] do
    if is_symmetric(n,k) then
      sym := sym+1;
    else
      non := non+1;
    fi;
  od;
  return sym+2*non;
end;


# For any semigroup, create (if they exist) all maps (up to iso) sigma
# such that
# 1. a+b=b+sigma_b(a)
# 2. sigma_a(b+c)=sigma_a(b)+sigma_a(c)
# 3. sigma_{a+b}(c) =\sigma_{b}\sigma_{a}(c)
# 4. sigma_{sigma_b(a)}(b) = b

create_file := function(n,k,m)
  local f,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  f := Filtered(fix(n,k), x->not x=());

  if f <> [] then

    perms := AsList(f);

    for k in perms do
      Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
      Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
    od;

    lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting M be ", String(m), "\n"),
    Concatenation("letting n be ", String(n), "\n"),
    "letting perms be [\n", tmp1, "]\n",
    "letting inverses be [\n", tmp2, "]\n",
    "find S : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    "forAll x,y : int(1..n) .",
    "  M[x,y]=M[y,S[y,x]],\n",
    "forAll x,y : int(1..n) .",
    "  S[S[y,x],y]=y,\n",
    "forAll x,y,z : int(1..n) .",
    "  S[x,M[y,z]]=M[S[x,y],S[x,z]],\n",
    "forAll x,y,z : int(1..n) .",
    "  S[M[x,y],z]=S[y,S[x,z]],\n",
    ];

    Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ S[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,S[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));
  else
    lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting M be ", String(m), "\n"),
    Concatenation("letting n be ", String(n), "\n"),
    "letting perms be [\n", tmp1, "]\n",
    "letting inverses be [\n", tmp2, "]\n",
    "find S : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    "forAll x,y : int(1..n) .",
    "  M[x,y]=M[y,S[y,x]],\n",
    "forAll x,y : int(1..n) .",
    "  S[S[y,x],y]=y,\n",
    "forAll x,y,z : int(1..n) .",
    "  S[x,M[y,z]]=M[S[x,y],S[x,z]],\n",
    "forAll x,y,z : int(1..n) .",
    "  S[M[x,y],z]=S[y,S[x,z]],\n",
    ];
  fi;

  Add(lines, "\ntrue\n");
  return lines;
end;

create_files := function(n)
  local f,x,s,k;

  for k in [1..NrSmallSemigroups(n)] do
    s := create_file(n,k);
    f := IO_File(Concatenation("eprime/derivedYBsemitruss", String(n), "_", String(k), ".eprime"), "w");
    k := k+1;
    for x in s do
      IO_WriteLine(f, x);
    od;
    IO_Flush(f);
    IO_Close(f);
  od;
end;

keep_derivedYBsemitruss := function(n, filename)
  local l, k, x, m, f, done;

  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
        k := k+1;
        Add(l, m);
      #fi;
    fi;
  od;
  Print("I found ", k, " cubic YB derived semitrusses.\n");
  IO_Close(f);
  return l;
end;



read_file := function(n, filename, T)
  local l, k, x, m, f, done;

  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      k := k+1;
      Add(l, m);
    fi;
  od;
  Print("I found ", k, " YB derived semitrusses\n");
  return l;
end;

run := function(filename, m, n, k)
  local s, l, f, x, t, output;

  t := [];
  l := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  Print("Running savilerow. ");
  output := Concatenation("output/output", String(n), "_", String(k));
  Exec(Concatenation(s,"eprime/", filename, ".eprime"," >", output));
  for x in keep_derivedYBsemitruss(n, output) do
    Add(t, x);
    l := l+1;
  od;

  f := IO_File(Concatenation("data/",filename, ".g"), "w");

  IO_WriteLine(f, Concatenation("semigroup", " := ", String(m), ";"));
  IO_WriteLine(f, Concatenation("sigma", " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),","));
  od;
  IO_WriteLine(f, "];\n\n");
  IO_Flush(f);
  IO_Close(f);

  return l;
end;

construct_derivedYBsemitruss := function(n)
  local filename, t0, t1, mytime, k, s, f, x, l;

  t0 := NanosecondsSinceEpoch();

  l := 0;

  LogTo();
  LogTo(Concatenation("log/derivedYBsemitruss", String(n), ".log"));

  for k in [1..NrSmallSemigroups(n)] do

    if is_symmetric(n,k) then
      s := create_file(n,k,RecoverMultiplicationTableNC(n,k));
      f := IO_File(Concatenation("eprime/derivedYBsemitruss", String(n), "_", String(k), ".eprime"), "w");
      for x in s do
        IO_WriteLine(f, x);
      od;
      IO_Flush(f);
      IO_Close(f);

      filename := Concatenation("derivedYBsemitruss", String(n), "_", String(k));
      l := l+run(filename, RecoverMultiplicationTableNC(n,k),  n, k);

   else
      s := create_file(n,k,RecoverMultiplicationTableNC(n,k));
      f := IO_File(Concatenation("eprime/derivedYBsemitruss", String(n), "_", String(k), "a.eprime"), "w");
      for x in s do
        IO_WriteLine(f, x);
      od;
      IO_Flush(f);
      IO_Close(f);

      filename := Concatenation("derivedYBsemitruss", String(n), "_", String(k), "a");
      l := l+run(filename, RecoverMultiplicationTableNC(n,k),  n, k);

      s := create_file(n,k,TransposedMat(RecoverMultiplicationTableNC(n,k)));
      f := IO_File(Concatenation("eprime/derivedYBsemitruss", String(n), "_", String(k), "b.eprime"), "w");
      for x in s do
        IO_WriteLine(f, x);
      od;
      IO_Flush(f);
      IO_Close(f);

      filename := Concatenation("derivedYBsemitruss", String(n), "_", String(k), "b");
      l := l+run(filename, TransposedMat(RecoverMultiplicationTableNC(n,k)),  n, k);

    fi;

  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", l, " cubic derived YB semitrusses in ", mytime, "ms (=", StringTime(mytime), ")\n");
end;


read_all := function(n)
  local t,x,k,list,semigroup,sigma;

  list := [];
  t := 0;

  for k in [1..NrSmallSemigroups(n)] do
    if is_symmetric(n,k) then
      Read(Concatenation(database_path, "/derivedYBsemitruss", String(n), "_", String(k), ".g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
    else
      Read(Concatenation(database_path, "/derivedYBsemitruss", String(n), "_", String(k), "a.g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
      Read(Concatenation(database_path,"/derivedYBsemitruss", String(n), "_", String(k), "b.g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
    fi;
    for x in sigma do
      Add(list, rec( semigroup := semigroup, sigma := x, size := Size(semigroup)));
    od;
  od;
  return list;
end;

run := function(filename, m, n, k)
  local s, l, f, x, t, output;

  t := [];
  l := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  Print("Running savilerow. ");
  output := Concatenation("output/output", String(n), "_", String(k));
  Exec(Concatenation(s,"eprime/", filename, ".eprime"," >", output));
  for x in keep_derivedYBsemitruss(n, output) do
    Add(t, x);
    l := l+1;
  od;

  f := IO_File(Concatenation("data/",filename, ".g"), "w");

  IO_WriteLine(f, Concatenation("semigroup", " := ", String(m), ";"));
  IO_WriteLine(f, Concatenation("sigma", " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),","));
  od;
  IO_WriteLine(f, "];\n\n");
  IO_Flush(f);
  IO_Close(f);

  return l;
end;

# 1. a+\lambda_a(b) = a·b
# 2. a·(b+c)= (a·b)+ lambda_a(c),
# 3. lambda_a(b+c)=lambda_a(b)+lambda_a(c)
# 4. lambda_a lambda_b =lambda_{a\circ b}
# 5. sigma_{lambda_a(c)}\lambda_a(b) = \lambda_a \sigma_c(b)

# # # First you need to find potential lambdas.
# # # For each potential lambda you need to check if you can find potential
# # # circle operations.

create_fileLambdas := function(semigroup,sigma,n,k)
  local f,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  # f := Filtered(fix(n,k), x->not x=());
  #
  # if f <> [] then
  #
  #   perms := AsList(f);
  #
  #   for k in perms do
  #     Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
  #     Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  #   od;

  # 1. a+\lambda_a(b) = a·b
  # 2. a·(b+c)= (a·b)+ lambda_a(c),
  # 3. lambda_a(b+c)=lambda_a(b)+lambda_a(c)
  # 4. lambda_a lambda_b =lambda_{a\circ b}
  # 5. sigma_{lambda_a(c)}\lambda_a(b) = \lambda_a \sigma_c(b)

    lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting M be ", String(semigroup), "\n"),
    Concatenation("letting S be ", String(sigma), "\n"),
    Concatenation("letting n be ", String(n), "\n"),
    # "letting perms be [\n", tmp1, "]\n",
    # "letting inverses be [\n", tmp2, "]\n",
    "find L : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    # "find C : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    # "forAll x,y : int(1..n) .",
    # "  M[x,L[x,y]]=C[x,y],\n",
    # "forAll x,y,z : int(1..n) .",
    # "  C[x,M[y,z]]=M[C[x,y],L[x,z]],\n",
    "forAll x,y,z : int(1..n) .",
    "  L[x,L[y,z]]=M[L[x,y],L[x,z]],\n",
    "forAll x,y,z : int(1..n) .",
    "  S[L[x,z],L[x,y]]=L[x,S[z,y]],\n",
    ];

    # Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    # flatten( [ S[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    # <=lex flatten( [ inverses[p,S[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));
  # else
  #   lines := [
  #   "language ESSENCE' 1.0\n",
  #   Concatenation("letting M be ", String(m), "\n"),
  #   Concatenation("letting n be ", String(n), "\n"),
  #   "letting perms be [\n", tmp1, "]\n",
  #   "letting inverses be [\n", tmp2, "]\n",
  #   "find S : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
  #   "such that\n",
  #   "forAll x,y : int(1..n) .",
  #   "  M[x,y]=M[y,S[y,x]],\n",
  #   "forAll x,y : int(1..n) .",
  #   "  S[S[y,x],y]=y,\n",
  #   "forAll x,y,z : int(1..n) .",
  #   "  S[x,M[y,z]]=M[S[x,y],S[x,z]],\n",
  #   "forAll x,y,z : int(1..n) .",
  #   "  S[M[x,y],z]=S[y,S[x,z]],\n",
  #   ];
  # fi;

  Add(lines, "\ntrue\n");
  return lines;
end;


keep_lambdas := function(n, filename)
  local l, k, x, m, f, done;

  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
        k := k+1;
        Add(l, m);
      #fi;
    fi;
  od;
  Print("I found ", k, " possible lambdas.\n");
  IO_Close(f);
  return l;
end;

run_lambdas := function(filename, semigroup, sigma, n, k)
  local s, l, f, x, t, output;

  t := [];
  l := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  Print("Running savilerow. ");
  output := Concatenation("output/outputLambda", String(n), "_", String(k));
  Exec(Concatenation(s,"eprime/", filename, ".eprime"," >", output));
  for x in keep_lambdas(n, output) do
    Add(t, x);
    l := l+1;
  od;

  f := IO_File(Concatenation("data/",filename, ".g"), "w");

  IO_WriteLine(f, Concatenation("semigroup", " := ", String(semigroup), ";"));
  IO_WriteLine(f, Concatenation("sigma", " :=", String(sigma), ";"));
  IO_WriteLine(f, Concatenation("lambda", " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),","));
  od;
  IO_WriteLine(f, "];\n\n");
  IO_Flush(f);
  IO_Close(f);

  return l;
end;

construct_lambdas := function(n)
  local derivedYBsemitrusses,derivedYBsemitruss, filename, t0, t1, mytime, k, s, f, x, l;

  t0 := NanosecondsSinceEpoch();

  l := 0;

  LogTo();
  LogTo(Concatenation("log/lambdas", String(n), ".log"));

  derivedYBsemitrusses:=read_all(n);

  k:=1;
  for derivedYBsemitruss in derivedYBsemitrusses do
    s:=create_fileLambdas(derivedYBsemitruss!.semigroup,derivedYBsemitruss!.sigma,n,k);
    f := IO_File(Concatenation("eprime/lambdas", String(n), "_", String(k), ".eprime"), "w");
    for x in s do
      IO_WriteLine(f, x);
    od;
    IO_Flush(f);
    IO_Close(f);
    filename := Concatenation("lambdas", String(n), "_", String(k));
    l := l+run_lambdas(filename, derivedYBsemitruss!.semigroup, derivedYBsemitruss!.sigma, n, k);
    k:=k+1;
  od;


  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", l, " possible lambdas in ", mytime, "ms (=", StringTime(mytime), ")\n");
end;



create_fileYB := function(semigroup,sigma,lambda,n,k)
  local f,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

    lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting M be ", String(semigroup), "\n"),
    Concatenation("letting S be ", String(sigma), "\n"),
    Concatenation("letting L be ", String(lambda), "\n"),
    Concatenation("letting n be ", String(n), "\n"),
    "find C : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    "forAll x,y : int(1..n) .",
    "  M[x,L[x,y]]=C[x,y],\n",
    "forAll x,y,z : int(1..n) .",
    "  C[x,M[y,z]]=M[C[x,y],L[x,z]],\n",
    ];


  Add(lines, "\ntrue\n");
  return lines;
end;


keep_YB := function(n, filename)
  local l, k, x, m, f, done;

  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
        k := k+1;
        Add(l, m);
      #fi;
    fi;
  od;
  Print("I found ", k, " possible cubic YB semitrusses.\n");
  IO_Close(f);
  return l;
end;

run_YB := function(filename, semigroup, sigma, lambda,n, k)
  local s, l, f, x, t, output;

  t := [];
  l := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  Print("Running savilerow. ");
  output := Concatenation("output/outputYB", String(n), "_", String(k));
  Exec(Concatenation(s,"eprime/", filename, ".eprime"," >", output));
  for x in keep_YB(n, output) do
    Add(t, x);
    l := l+1;
  od;

  f := IO_File(Concatenation("data/",filename, ".g"), "w");

  IO_WriteLine(f, Concatenation("semigroup", " := ", String(semigroup), ";"));
  IO_WriteLine(f, Concatenation("sigma", " :=", String(sigma), ";"));
  IO_WriteLine(f, Concatenation("lambda", " :=", String(lambda), ";"));
  IO_WriteLine(f, Concatenation("circ", " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),","));
  od;
  IO_WriteLine(f, "];\n\n");
  IO_Flush(f);
  IO_Close(f);

  return l;
end;

read_all_lambda := function(n)
  local t,x,k,list,semigroup,sigma,lambda,l;

  list := [];
  t := 0;

  for k in [1..NrSmallSemigroups(n)] do
    if is_symmetric(n,k) then
      Read(Concatenation(database_path, "/derivedYBsemitruss", String(n), "_", String(k), ".g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
    else
      Read(Concatenation(database_path, "/derivedYBsemitruss", String(n), "_", String(k), "a.g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
      Read(Concatenation(database_path,"/derivedYBsemitruss", String(n), "_", String(k), "b.g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      t := t+Size(sigma);
    fi;
      od;
    l:=0;
    for k in [1..t] do
      Read(Concatenation(database_path, "/lambdas", String(n), "_", String(k), ".g"));
      semigroup := EvalString("semigroup");
      sigma := EvalString("sigma");
      lambda:=EvalString("lambda");
      l := l+Size(lambda);
      for x in lambda do
        Add(list, rec( semigroup := semigroup, sigma := sigma, lambda:=x ,size := Size(semigroup)));
      od;
  od;
  return list;
end;

construct_YB := function(n)
  local potentialYBsemitrusses,potentialYBsemitruss, filename, t0, t1, mytime, k, s, f, x, l;

  t0 := NanosecondsSinceEpoch();

  l := 0;

  LogTo();
  LogTo(Concatenation("log/YB", String(n), ".log"));

  potentialYBsemitrusses:=read_all_lambda(n);

  k:=1;
  for potentialYBsemitruss in potentialYBsemitrusses do
    s:=create_fileYB(potentialYBsemitruss!.semigroup,potentialYBsemitruss!.sigma,potentialYBsemitruss!.lambda,n,k);
    f := IO_File(Concatenation("eprime/YB", String(n), "_", String(k), ".eprime"), "w");
    for x in s do
      IO_WriteLine(f, x);
    od;
    IO_Flush(f);
    IO_Close(f);
    filename := Concatenation("YB", String(n), "_", String(k));
    l := l+run_YB(filename, potentialYBsemitruss!.semigroup, potentialYBsemitruss!.sigma, potentialYBsemitruss!.lambda,n, k);
    k:=k+1;
  od;


  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", l, " cubic YB semitrusses in ", mytime, "ms (=", StringTime(mytime), ")\n");
end;
