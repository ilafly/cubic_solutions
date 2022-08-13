LoadPackage("SmallSemi");

is_automorphism := function(f,n,k)
  local m,x,y;
  m := RecoverMultiplicationTable(n,k);
  for x in [1..n] do
    for y in [1..n] do
      if not m[x][y]^f = m[x^f][y^f] then
        return false;
      fi;
    od;
  od;
  return true;
end;

automorphism_group := function(n,k)
  local l;
  l := Filtered(SymmetricGroup(n), f->is_automorphism(f, n, k));
  return Group(l);
end;
