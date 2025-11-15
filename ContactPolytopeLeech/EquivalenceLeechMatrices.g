GetTheEquivalence:=function(GramMat1, GramMat2)
  local SHV1, SHV2, n, GRPanti
  SHV1:=ShortestVectorDutourVersion(GramMat1);
  SHV2:=ShortestVectorDutourVersion(GramMat2);
  n:=Length(GramMat1);
  GRPanti:=Group([-IdentityMat(n)]);
  O1:=Orbits(GRPanti, SHV1);
  O2:=Orbits(GRPanti, SHV2);
  nbOrb:=Length(O1);
  GRA1:=NullGraph(Group(()), nbOrb);
  for i in [1..nbOrb-1]
  do
    eVect1:=O1[i][1];
    for j in [i+1..nbOrb]
    do
      eVect2:=O1[j][1];
      eScal:=AbsInt(eVect1*GramMat1*eVect2);
      if eScal=1/2 then
        AddEdgeOrbit(GRA1, [i,j]);
        AddEdgeOrbit(GRA1, [j,i]);
      fi;
    od;
  od;
  Print("We have GRA1\n");
  GRA2:=NullGraph(Group(()), nbOrb);
  for i in [1..nbOrb-1]
  do
    eVect1:=O2[i][1];
    for j in [i+1..nbOrb]
    do
      eVect2:=O2[j][1];
      eScal:=AbsInt(eVect1*GramMat2*eVect2);
      if eScal=1/2 then
        AddEdgeOrbit(GRA2, [i,j]);
        AddEdgeOrbit(GRA2, [j,i]);
      fi;
    od;
  od;
  Print("We have GRA2\n");
  eIso:=EquivalenceVertexColoredGraph(GRA1, GRA2, [[1..nbOrb]]);
  return eIso;
end;
