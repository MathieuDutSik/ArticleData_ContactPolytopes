GramMat:=ReadAsFunction("GramMat")();
n:=Length(GramMat);

GRP:=ReadAsFunction("LeechGroup")();
SHV:=ReadAsFunction("LeechNeigh")();

ListScal:=List(SHV, x->x*GramMat*SHV[1]);
SetScal:=Set(ListScal);

ListSumVect:=[];
ListNorm:=[];
ListNB:=[];
for eScal in SetScal
do
  ThePos:=Position(ListScal, eScal);
  TheSumVect:=SHV[1]+SHV[ThePos];
  Add(ListSumVect, TheSumVect);
  TheNorm:=TheSumVect*GramMat*TheSumVect;
  TheNB:=Length(Filtered(ListScal, x->x=eScal));
  Add(ListNorm, TheNorm);
  Add(ListNB, TheNB);
od;
Pos:=Position(ListNorm, 6);
TheVect6:=ListSumVect[Pos];

ListScal6:=List(SHV, x->x*GramMat*TheVect6);
SetScal6:=Set(ListScal6);
ListNB6:=List(SetScal6, x->Length(Filtered(ListScal6, y->y=x)));

Pos:=Position(ListNB6, 552);
SelectScal:=SetScal6[Pos];

Set552:=Filtered([1..Length(ListScal6)], x->ListScal6[x]=SelectScal);


nbV:=Length(Set552);
DistMat:=NullMat(nbV, nbV);
for i in [1..nbV-1]
do
  for j in [i+1..nbV]
  do
    eDiff:=SHV[Set552[i]]-SHV[Set552[j]];
    eNorm:=eDiff*GramMat*eDiff;
    DistMat[i][j]:=eNorm;
    DistMat[j][i]:=eNorm;
  od;
od;
GRPstab:=AutomorphismGroupEdgeColoredGraph(DistMat);


ListPermGen:=GetListPermGens(SHV, GeneratorsOfGroup(GRP));
PermGRP:=Group(ListPermGen);
SetSize(PermGRP, Order(GRP));

TheStab:=Stabilizer(PermGRP, Set552, OnSets);
