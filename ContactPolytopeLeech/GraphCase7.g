ListEdges:=[
[1,3],
[3,4],
[4,2],
[1,2],

[5,6],
[6,8],
[7,8],
[5,7],

[9,10],
[10,12],
[11,12],
[9,11],

[2,12],
[3,9],

[5,10],
[8,11],

[4,6],
[1,7]];

GRA:=NullGraph(Group(()), 12);

for eEdge in ListEdges
do
  AddEdgeOrbit(GRA, eEdge);
  AddEdgeOrbit(GRA, Reversed(eEdge));
od;

GRP:=AutGroupGraph(GRA);

PL:=ArchimedeanPolyhedra("Cube");
TheCube:=PlanGraphToGRAPE(PL);

GRP2:=AutGroupGraph(TheCube);
