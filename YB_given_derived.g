LoadPackage("IO");
LoadPackage("YangBaxter");
Read("derived_v3.g");

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

is_isomorphism_YB := function(f, r, s)
  local x, y, u, v;
	for x in [1..Size(r)] do
		for y in [1..Size(r)] do
			u := YB_xy(r, x, y)[1];
			v := YB_xy(r, x, y)[2];
			if not [u^f, v^f] = YB_xy(s, x^f, y^f) then
				return false;
			fi;
		od;
 	od;
	return true;
end;

isomorphism_YB := function(r, s)
	return true in List(SymmetricGroup(Size(r)), f->is_isomorphism_YB(f, r, s));
end;

shelfandlambda2YB := function(rack, matrix)
  local x,y,m,n,rhos,lambdas,tmp;
  n := Size(rack);
  tmp := List(matrix, x->Inverse(PermList(x)));
  lambdas := List(tmp, x->List(ListPerm(x,n),y->y));
  rhos := NullMat(n,n);
  for x in [1..n] do
    for y in [1..n] do
      rhos[y][x] := matrix[lambdas[x][y]][rack[lambdas[x][y]][x]];
    od;
  od;
  return [lambdas, rhos];
end;

is_automorphism := function(f, rack)
  local x,y;
  for x in [1..Size(rack)] do
    for y in [1..Size(rack)] do
      if rack[x][y]^f <> rack[x^f][y^f] then
        return false;
      fi;
    od;
  od;
  return true;
end;

fixed := function(rack)
  return Filtered(SymmetricGroup(Size(rack)), x->twist_matrix(rack, x)=rack and is_automorphism(x,rack));
end;

create_files := function(n, racks)
  local x,f,k,s,m,lines,perms,tmp1,tmp2,rack;

  m := 0;

  for rack in racks do
    tmp1 := "";
    tmp2 := "";

    perms := SymmetricGroup(n);
    perms := fixed(rack);

    for k in perms do
      Append(tmp1, Concatenation(String(List(ListPerm(k,n),y->y)),",\n"));
      Append(tmp2, Concatenation(String(List(ListPerm(Inverse(k),n),y->y)),",\n"));
    od;

    m := m+1;

    lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting n be ", String(n), "\n"),
    "letting perms be [", tmp1, "]\n",
    "letting inverses be [\n", tmp2, "]\n",
    "letting rack be \n", rack, "\n",
    "find M : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    "forAll x : int(1..n) .",
    "  allDiff(M[x,..]),\n",
    "forAll x,y,z : int(1..n) .",
    "  M[M[x,rack[x,y]],M[x,z]]=M[M[y,x],M[y,z]],\n",
    "forAll x,y,z : int(1..n) .",
    "  M[x,rack[y,z]]=rack[M[x,y],M[x,z]],"
    ];

    Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
      flatten( [ M[i,j] | i : int(1..n), j : int(1..n)] )\n\\
      <=lex flatten( [ inverses[p,M[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

    Add(lines, "\ntrue\n");

    f := IO_File(Concatenation("eprime/solutions/YB", String(n), "_r", String(m),".eprime"), "w");
    for x in lines do
      IO_WriteLine(f, x);
    od;
    IO_Flush(f);
    IO_Close(f);
  od;

  return;
end;

read_file := function(n, filename)
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
  Print("I found ", k, " cubic solutions\n");

  IO_Flush(f);
  IO_Close(f);

  return l;
end;

compute_YB := function(n,racks)
  local m,l,T,k,s,f,x,t,input, output, t0, t1, mytime, rack;

  t0 := NanosecondsSinceEpoch();

  k := 1;
  m := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("log/solutions/YB", String(n), "_method1.log"));

  create_files(n, racks);

  for rack in racks do

    t := [];

    # if rack = List([1..n], x->[1..n]) then
    #   Print("I skip the trivial rack.\n");
    #   k := k+1;
    #   continue;
    # fi;

    output := Concatenation("output/solutionsYB", String(n), "_r", String(k),".output");
    Print("Running savilerow. File: YB", String(n), "_r", String(k), ".eprime", ". Output: ", output, "\n");
    Exec(Concatenation(s, "eprime/solutions/YB", String(n), "_r", String(k), ".eprime", " >", output));

    for x in read_file(n, output) do
      Add(t, shelfandlambda2YB(rack,x));
      m := m+1;
    od;

    t1 := NanosecondsSinceEpoch();
    mytime := Int(Float((t1-t0)/10^6));
    Print("Rack:\n");
    Display(rack);
    Print("I constructed ", m, " cubic solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

    f := IO_File(Concatenation("data/solutions/YB", String(n), "_r", String(k), ".g"), "w");
    IO_WriteLine(f, Concatenation("data/solutions/YB", String(n), "_r", String(k)," := ["));
    for x in t do
      IO_WriteLine(f, Concatenation(String(x),","));
    od;

    IO_WriteLine(f, "];");
    IO_Flush(f);
    IO_Close(f);

    k := k+1;
  od;
end;

cubic_solutions:=function(n)
  local racks;
  racks:=read_derived_solutions(n);
  compute_YB(n,racks);
end;

enumerate_YB := function(n,racks)
  local m,l, T,k,s,f,x,t,input, output, t0, t1, mytime, rack;

  t0 := NanosecondsSinceEpoch();

  k := 1;
  m := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("log/solutions/YB", String(n), "_method1.log"));

  create_files(n, racks);

  for rack in racks do

    t := [];

    if rack = List([1..n], x->[1..n]) then
      Print("I skip the trivial rack.\n");
      k := k+1;
      continue;
    fi;

    output := Concatenation("output/solutions/YB", String(n), "_r", String(k),".output");
    Print("Running savilerow. File: YB", String(n), "_r", String(k), ".eprime", ". Output: ", output, "\n");
    Exec(Concatenation(s, "eprime/solutions/YB", String(n), "_r", String(k), ".eprime", " >", output));

    t := Size(read_file(n, output));
    m := m+t;

    t1 := NanosecondsSinceEpoch();
    mytime := Int(Float((t1-t0)/10^6));
    Print("Rack:\n");
    Display(rack);
    Print("I constructed ", m, " cubic solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

    k := k+1;
  od;
end;

first_condition:=function(lambdas,rhos,x,y,z)
  return lambdas[x][lambdas[y][z]] = lambdas[lambdas[x][y]][lambdas[rhos[y][x]][z]];
end;

second_condition:=function(lambdas,rhos,x,y,z)
  return lambdas[rhos[lambdas[y][z]][x]][rhos[z][y]] = rhos[lambdas[rhos[y][x]][z]][lambdas[x][y]];
end;

third_condition:=function(lambdas,rhos,x,y,z)
  return rhos[y][rhos[y][x]]=rhos[rhos[z][y]][rhos[lambdas[y][z]][x]];
end;

is_solution:=function(lambdas,rhos)
  local n,x,y,z;
  n:=Size(lambdas);
  for x in [1..n] do
    for y in [1..n] do
      for z in [1..n] do
        if first_condition(lambdas,rhos,x,y,z) = false then
          return false;
        fi;
        if second_condition(lambdas,rhos,x,y,z) = false then
          return false;
        fi;
        if third_condition(lambdas,rhos,x,y,z) = false then
          return false;
        fi;
      od;
    od;
  od;
  return true;
end;

is_involutive:=function(lambdas,rhos)
  local n,x,y;
  n:=Size(lambdas);
  for x in [1..n] do
    for y in [1..n] do
      if (lambdas[lambdas[x][y]][rhos[y][x]]=x) =false then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_idempotent:=function(lambdas,rhos)
  local n,x,y;
  n:=Size(lambdas);
  for x in [1..n] do
    for y in [1..n] do
      if (lambdas[lambdas[x][y]][rhos[y][x]]=lambdas[x][y]) =false then
        return false;
      fi;
    od;
  od;
  return true;
end;
