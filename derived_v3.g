LoadPackage("IO");
Read("lib/aut.g");


# The following functions allows one to check if in the list of shelf
# there are repetitions.

read_derived_solutions:=function(n)
  local f,sols;
  f := Concatenation("data/solutions/cubic", String(n), "derived" ,".g");
  Read(f);
  sols := EvalString("sols");
  return sols;
end;

is_isomorphism_derived := function(f, sigma1, sigma2)
  local x, y, u, v;
	for x in [1..Size(sigma1)] do
		for y in [1..Size(sigma1)] do
			v:= y^f;
      u:=x^f;
			if not sigma1[v][u] = (sigma2[y][x])^f then
				return false;
			fi;
		od;
 	od;
	return true;
end;

isomorphism_derived := function(r, s)
	return true in List(SymmetricGroup(Size(r)), f->is_isomorphism_derived(f, r, s));
end;

is_involutive_derived:=function(s)
  local x,y;
  for x in [1..Size(s)] do
    for y in [1..Size(s)] do
      if not s[y][x]= x then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_idempotent_derived:=function(s)
  local x,y;
  for x in [1..Size(s)] do
		for y in [1..Size(s)] do
      if not s[y][x]= y then
        return false;
      fi;
    od;
  od;
  return true;
end;

is_new := function(list, sol)
  local sigma;
  for sigma in list do
     if isomorphism_derived(sigma,sol) then
       return false;
     fi;
  od;
  return true;
end;

up_to_iso_derived:=function(n)
  local sols,r,s, sols_up_to_iso;
  sols:=read_derived_solutions(n);
  sols_up_to_iso:=[];
  Add(sols_up_to_iso, sols[1]);
  for r in sols do
    if is_new(sols_up_to_iso,r) then
      Add(sols_up_to_iso,r);
    fi;
  od;
  return sols_up_to_iso;
end;


# create cubic shelf up to isomorphism
create_content_derived := function(n)
  local f,lines,perms,k,tmp1,tmp2, cc,c;

  tmp1 := "";
  tmp2 := "";
  perms := AsList(SymmetricGroup(n)){[2..Factorial(n)]};;

  # if n<6 then
  #   perms := AsList(SymmetricGroup(n)){[2..Factorial(n)]};;
  # else
  #   perms := AsList(SymmetricGroup(n)){[2..Factorial(5)]};;
  # fi;

  # perms:=ShallowCopy(AsList(ConjugacyClass(SymmetricGroup(n),(1,2))));

  # if n>4 then
  #   Append(perms,AsList(ConjugacyClass(SymmetricGroup(n),(1,2)(3,4))));
  # fi;
  # if n>6 then
  #   Append(perms,AsList(ConjugacyClass(SymmetricGroup(n),(1,2)(3,4)(6,7))));
  #   Append(perms,AsList(ConjugacyClass(SymmetricGroup(n),(1,2,3,4)(6,7))));
  # fi;

  for k in perms do
    Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
    Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  od;

  lines := [
    "language ESSENCE' 1.0\n",
    Concatenation("letting n be ", String(n), "\n"),
    "letting perms be [\n", tmp1, "]\n",
    "letting inverses be [\n", tmp2, "]\n",
    "find S : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
    "such that\n",
    "forAll x,y : int(1..n) .",
    "     S[S[y,x],y] = y,\n",
    "forAll x,y,z : int(1..n) .",
    "  S[S[z,y],S[z,x]]=S[z,S[y,x]],"
    ];

    Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ S[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,S[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

    Add(lines, "\ntrue\n");
  return lines;
end;

create_file_derived := function(n)
  local f,x,s,k;

  s := create_content_derived(n);
  f := IO_File(Concatenation("eprime/solutions/cubic", String(n), "derived" ,".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
end;


create_file := function(n)
  local f,x,s,k;

  s := create_content_derived(n);
  f := IO_File(Concatenation("eprime/solutions/cubic", String(n), "derived" ,".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
end;


keep_cubic := function(n, filename)
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
  Print("I found ", k, " derived solutions.\n");
  IO_Close(f);
  return l;
end;

run := function(filename, n)
  local s, l, f, x, t, output;

  t := [];
  l := 0;
  s := "../savilerow-1.9.1-mac/savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  Print("Running savilerow. ");
  output := Concatenation("output/solutions/output", String(n));
  Exec(Concatenation(s, "eprime/solutions/",filename,".eprime", " >", output));
  for x in keep_cubic(n, output) do
    # if is_new(t,x) then
      Add(t, x);
      l := l+1;
    # fi;
  od;

  f := IO_File(Concatenation("data/solutions/",filename, ".g"), "w");

  IO_WriteLine(f, Concatenation("sols", " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),","));
  od;
  IO_WriteLine(f, "];\n\n");
  IO_Flush(f);
  IO_Close(f);

  return l;
end;


derived_cubic_solutions:=function(n)
  local f, filename,l,s,x,mytime,t0,t1;

  t0 := NanosecondsSinceEpoch();

  LogTo();
  LogTo(Concatenation("log/solutions/cubic", String(n), ".log"));


  s := create_content_derived(n);
  f := IO_File(Concatenation("eprime/solutions/cubic", String(n), "derived", ".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);

  filename := Concatenation("cubic", String(n), "derived");
  l:=run(filename,  n);


  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));

  Print("I constructed ", l, " derived cubic soultions of the YBE in ", mytime, "ms (=", StringTime(mytime), ")\n");
end;
