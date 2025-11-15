GramMat:=ReadAsFunction("GramMat")();;
SHV:=ReadAsFunction("LeechNeigh")();
GRP:=ReadAsFunction("LeechGroup")();
FileSHV_ListPermGens:="Database/SAVE_ListPermGens";
if IsExistingFilePlusTouch(FileSHV_ListPermGens)=true then
  SHV_ListPermGen:=ReadAsFunction(FileSHV_ListPermGens)();
else
  SHV_ListPermGen:=GetListPermGens(SHV, GeneratorsOfGroup(GRP));
  SaveDataToFilePlusTouch(FileSHV_ListPermGens, SHV_ListPermGen);
fi;
SHV_PermGRP:=Group(SHV_ListPermGen);
SetSize(SHV_PermGRP, Order(GRP));

ListOrbitEXT:=ReadAsFunction("ListOrbitEXT")();

GetDistOrigin:=function(ListVect)
  local ListEqua, ListB, eVect, eCent;
  ListEqua:=[];
  ListB:=[];
  for eVect in ListVect
  do
    Add(ListEqua, 2*eVect*GramMat);
    Add(ListB, 1);
  od;
  eCent:=SolutionMat(TransposedMat(ListEqua), ListB);
  return rec(eVert:=eCent, eSqr:=eCent*GramMat*eCent);
end;


FileContactStabilizer:="Database/ContactStabilizers";
if IsExistingFilePlusTouch(FileContactStabilizer)=false then
  ListContactStabilizers:=[];
  for eOrb in ListOrbitEXT
  do
    eStab:=Stabilizer(SHV_PermGRP, eOrb, OnSets);
    eStabRed:=SecondReduceGroupAction(eStab, eOrb);
    Add(ListContactStabilizers, eStabRed);
  od;
  SaveDataToFilePlusTouch(FileContactStabilizer, ListContactStabilizers);
else
  ListContactStabilizers:=ReadAsFunction(FileContactStabilizer)();
fi;
SizeCoZero:=8315553613086720000;
TotalNumberVertices:=0;
for eStabRed in ListContactStabilizers
do
  TotalNumberVertices:=TotalNumberVertices + SizeCoZero/Order(eStabRed);
od;
Print("TotalNumberVertices=",TotalNumberVertices, "\n");




GetAllInfos:=function(EXTdelaunay, typecall)
  local eCenterDel, ThePair, AffBas, NeedAffBas, TheINF;
  eCenterDel:=Isobarycenter(EXTdelaunay);
  ThePair:=CharacterizingPair(GramMat, eCenterDel);
  AffBas:="irrelevant";
  NeedAffBas:=false;
  TheINF:=FuncMethod6_SVR(GramMat, SHV, AffBas, EXTdelaunay, eCenterDel, ThePair[1], typecall, NeedAffBas);
  return rec(ThePair:=ThePair, SVR:=TheINF.SVR);
end;



TestEquivalenceDelaunayMethod:=function(EXTdelaunay1, EXTdelaunay2)
  local AllInfos1, AllInfos2, TheTest, WorkMat, eMat, ListPerm, eRetPerm;
  AllInfos1:=GetAllInfos(EXTdelaunay1, "isomorphy");
  AllInfos2:=GetAllInfos(EXTdelaunay2, "isomorphy");
  TheTest:=ArithmeticEquivalenceMatrixFamily_Nauty(AllInfos1.ThePair, AllInfos1.SVR, AllInfos2.ThePair, AllInfos2.SVR);
  if TheTest=false then
    return false;
  fi;
  return true;
end;


StabilizerDelaunayMethod:=function(EXTdelaunay)
  local AllInfos, TheGRP, ListSmallGens, eMat, sSmallMat, ListPermGens, eGen, RetGRP, eSmallMat, eList;
  AllInfos:=GetAllInfos(EXTdelaunay, "automorphy");
  Print("|SVR|=", Length(AllInfos.SVR), "\n");
  TheGRP:=ArithmeticAutomorphismMatrixFamily_Nauty(AllInfos.ThePair, AllInfos.SVR);
  ListSmallGens:=[];
  for eMat in GeneratorsOfGroup(TheGRP)
  do
    if eMat[1][1]=1 then
      Add(ListSmallGens, eMat);
    else
      Add(ListSmallGens, -eMat);
    fi;
  od;
#  ListPermGen:=GetListPermGens(EXTdelaunay, ListSmallGens);
  ListPermGens:=[];
  for eMat in ListSmallGens
  do
    eList:=List(EXTdelaunay, x->Position(EXTdelaunay, x*eMat));
    Add(ListPermGens, PermList(eList));
  od;
  RetGRP:=Group(ListPermGens);
  SetSize(RetGRP, Order(TheGRP)/2);
  return RetGRP;
end;



GetBorcherdsStyleSymbol:=function(ListVect)
  local nbVect, LeechDistMat, iVect, jVect, eDiff, eDist, CoxeterMat, H, eStr, i, hStr, nb, ListInfo;
  nbVect:=Length(ListVect);
  LeechDistMat:=NullMat(nbVect, nbVect);
  for iVect in [1..nbVect-1]
  do
    for jVect in [iVect+1..nbVect]
    do
      eDiff:=ListVect[iVect]-ListVect[jVect];
      eDist:=eDiff*GramMat*eDiff;
      LeechDistMat[iVect][jVect]:=eDist;
      LeechDistMat[jVect][iVect]:=eDist;
    od;
  od;
  CoxeterMat:=LeechMatToCoxeterMat(LeechDistMat);
  ListInfo:=GetInformation_FiniteAffineGroupDynkinDiagram(CoxeterMat);
  H:=Collected(ListInfo.ListNamesLatexConway);
  eStr:="";
  for i in [1..Length(H)]
  do
    if i>1 then
      eStr:=Concatenation(eStr, ", ");
    fi;
    hStr:=H[i][1];
    nb:=H[i][2];
    if nb=1 then
      eStr:=Concatenation(eStr, hStr);
    else
      eStr:=Concatenation(eStr, hStr, "^{", String(nb), "}");
    fi;
  od;
  return eStr;
end;


FileInformationPrev:="Database/ThePrevInformations";
if IsExistingFilePlusTouch(FileInformationPrev)=false then
  ListInformationsPrev:=[];
  for iOrbit in [1..Length(ListOrbitEXT)]
  do
    Print("iOrbit=", iOrbit, "\n");
    eOrbit:=ListOrbitEXT[iOrbit];
    eVert1:=ListWithIdenticalEntries(25,0);
    eVert1[1]:=1;
    EXT:=Concatenation([eVert1], List(SHV{eOrbit}, x->Concatenation([1],x)));
    EXTred:=List(EXT, x->x{[2..25]});
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
    eCenter:=CP.Center;
    eCenterRed:=eCenter{[2..25]};
    TheCVP:=CVPVallentinProgram(GramMat, eCenterRed);
    EXTnearest:=List(TheCVP.ListVect, x->Concatenation([1], x));
    EXTnearestRed:=List(EXTnearest, x->x{[2..25]});
    SqrINFO:=GetDistOrigin(SHV{eOrbit});
    SqrDist:=SqrINFO.eSqr;
    if Set(EXTnearest)=Set(EXT) then
      DelaunayStatus:="It is Delaunay";
      if TheCVP.TheNorm<>CP.SquareRadius then
        Print("Inconsistency of some sort 1\n");
        Print(NullMat(5));
      fi;
    else
      if IsSubset(Set(EXTnearest), Set(EXT)) then
        DelaunayStatus:="It is defining a Delaunay";
        if TheCVP.TheNorm<>CP.SquareRadius then
          Print("Inconsistency of some sort 1\n");
          Print(NullMat(5));
        fi;
      else
        DelaunayStatus:="It is something else";
      fi;
    fi;
    if DelaunayStatus="It is something else" then
      TheSymbolTotalDelaunay:="irrelevant";
      TheSymbolPartialDelaunay:="irrelevant";
    else
      TheSymbolTotalDelaunay:=GetBorcherdsStyleSymbol(EXTnearestRed);
      TheSymbolPartialDelaunay:=GetBorcherdsStyleSymbol(EXTred);
    fi;
    ListInformationsPrev[iOrbit]:=
     rec(Sqr1:=TheCVP.TheNorm, Sqr2:=CP.SquareRadius, Sqr3:=SqrDist, 
         eVert:=SqrINFO.eVert, 
         eCenter:=eCenter, 
         EXTnearest:=EXTnearest, 
         DelaunayStatus:=DelaunayStatus,
         TheSymbolTotalDelaunay:=TheSymbolTotalDelaunay, 
         TheSymbolPartialDelaunay:=TheSymbolPartialDelaunay, 
         eCenterRed:=eCenterRed, 
         nbV:=Length(EXT));
  od;
  SaveDataToFilePlusTouch(FileInformationPrev, ListInformationsPrev);
else
  ListInformationsPrev:=ReadAsFunction(FileInformationPrev)();
fi;



ListNotDelaunay:=Filtered([1..Length(ListOrbitEXT)], x->ListInformationsPrev[x].DelaunayStatus="It is something else");
ListDelaunay:=Difference([1..Length(ListOrbitEXT)], ListNotDelaunay);





Is_a1pow25_Orbit:=function(EXTdelaunay)
  local EXTdelaunayRed, i, j, eDiff, eDist;
  if Length(EXTdelaunay)<>25 then
    return false;
  fi;
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  for i in [1..24]
  do
    for j in [i+1..25]
    do
      eDiff:=EXTdelaunayRed[i]-EXTdelaunayRed[j];
      eDist:=eDiff*GramMat*eDiff;
      if eDist<>4 then
        return false;
      fi;
    od;
  od;
  return true;
end;


GetSingularVertex_a1pow25_Orbit:=function(EXTdelaunay)
  local eIso, ListDiff, ListDiffRed, GetScalInfo, ListInvariant, TheCollected, ListSizes, pos, eInv, eIdx, ListDist;
  if Is_a1pow25_Orbit(EXTdelaunay)=false then
    Print("This is not correct function call\n");
    Print(NullMat(5));
  fi;
  eIso:=Isobarycenter(EXTdelaunay);
  ListDiff:=List(EXTdelaunay, x->x-eIso);
  ListDiffRed:=List(ListDiff, x->x{[2..25]});
  ListDist:=List(ListDiffRed, x->x*GramMat*x);
  if Length(Set(ListDist))<>1 then
    Print("We have inconsistency\n");
    Print(NullMat(5));
  fi;
  GetScalInfo:=function(eVect)
    local eProd;
    eProd:=eVect*GramMat;
    return GetCollectedList(SHV, x->eProd*x).TheCollected;
  end;
  ListInvariant:=List(ListDiffRed, GetScalInfo);
  TheCollected:=Collected(ListInvariant);
  ListSizes:=List(TheCollected, x->x[2]);
  if Set(ListSizes)<>[1,24] then
    Print("We have an inconsistency\n");
    Print(NullMat(5));
  fi;
  pos:=Position(ListSizes, 1);
  eInv:=TheCollected[pos][1];
  eIdx:=Position(ListInvariant, eInv);
  return eIdx;
end;


GetStabilizer_a1pow25_Orbit:=function(EXTdelaunay)
  local eIdx, EXTdelaunayRed, GRP, ListPermGen, ListDiff, ListPts, i, fIdx, eVect, pos, SetPts, ListPermGens, eGen, eList, h1, h2, h3, h4, h5, eStab, ListMatrGens, ePerm, GRPmat, eBigMat;
  eIdx:=GetSingularVertex_a1pow25_Orbit(EXTdelaunay);
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  ListDiff:=Difference([1..25], [eIdx]);
  ListPts:=[];
  for i in [1..24]
  do
    fIdx:=ListDiff[i];
    eVect:=EXTdelaunayRed[fIdx]-EXTdelaunayRed[eIdx];
    pos:=Position(SHV, eVect);
    Add(ListPts, pos);
  od;
  SetPts:=Set(ListPts);
  eStab:=Stabilizer(SHV_PermGRP, SetPts, OnSets);
  ListPermGens:=[];
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(eStab)
  do
    eList:=[];
    eList[eIdx]:=eIdx;
    for i in [1..24]
    do
      h1:=ListDiff[i];
      h2:=ListPts[i];
      h3:=OnPoints(h2, eGen);
      h4:=Position(ListPts, h3);
      h5:=ListDiff[h4];
      eList[h1]:=h5;
    od;
    ePerm:=PermList(eList);
    Add(ListPermGens, ePerm);
    eBigMat:=__LemmaFindTransformation(EXTdelaunay, EXTdelaunay, ePerm);
    Add(ListMatrGens, FuncExplodeBigMatrix(eBigMat).MatrixTransformation);
  od;
  GRPmat:=Group(ListMatrGens);
  SetSize(GRPmat, Order(Group(ListPermGens)));
  return GRPmat;
end;


TestEquivalence_a1pow25_Orbit:=function(EXTdelaunay1, EXTdelaunay2)
  local eIdx1, eIdx2, EXTdelaunay1Red, EXTdelaunay2Red, ListDiff1, ListDiff2, ListPts1, i, fIdx, eVect, pos, SetPts1, ListPts2, SetPts2, eRepr, eList, h1, h2, h3, h4, h5, ePerm, eBigMat;
  Print("We are in TestEquivalence_a1pow25_Orbit\n");
  eIdx1:=GetSingularVertex_a1pow25_Orbit(EXTdelaunay1);
  eIdx2:=GetSingularVertex_a1pow25_Orbit(EXTdelaunay2);
  EXTdelaunay1Red:=List(EXTdelaunay1, x->x{[2..25]});
  EXTdelaunay2Red:=List(EXTdelaunay2, x->x{[2..25]});
  ListDiff1:=Difference([1..25], [eIdx1]);
  ListDiff2:=Difference([1..25], [eIdx2]);
  ListPts1:=[];
  for i in [1..24]
  do
    fIdx:=ListDiff1[i];
    eVect:=EXTdelaunay1Red[fIdx]-EXTdelaunay1Red[eIdx1];
    pos:=Position(SHV, eVect);
    Add(ListPts1, pos);
  od;
  SetPts1:=Set(ListPts1);
  ListPts2:=[];
  for i in [1..24]
  do
    fIdx:=ListDiff2[i];
    eVect:=EXTdelaunay2Red[fIdx]-EXTdelaunay2Red[eIdx2];
    pos:=Position(SHV, eVect);
    Add(ListPts2, pos);
  od;
  SetPts2:=Set(ListPts2);
  eRepr:=RepresentativeAction(SHV_PermGRP, SetPts1, SetPts2, OnSets);
  eList:=[];
  eList[eIdx1]:=eIdx2;
  for i in [1..24]
  do
    h1:=ListDiff1[i];
    h2:=ListPts1[i];
    h3:=OnPoints(h2, eRepr);
    h4:=Position(ListPts2, h3);
    h5:=ListDiff2[h4];
    eList[h1]:=h5;
  od;
  ePerm:=PermList(eList);
  eBigMat:=__LemmaFindTransformation(EXTdelaunay1, EXTdelaunay2, ePerm);
  if IsIntegralMat(eBigMat)=false then
    Print("There is a problem somewhere\n");
    Print(NullMat(5));
  fi;
  return eBigMat;
end;

Is_A2pow12_Orbit:=function(EXTdelaunay)
  local nbV, EXTdelaunayRed, GRA, DistMat, i, j, eDiff, eDist, ListConn, eConn, eVert;
  nbV:=Length(EXTdelaunay);
  if nbV<>36 then
    return false;
  fi;
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  GRA:=NullGraph(Group(()), nbV);
  DistMat:=NullMat(nbV, nbV);
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      eDiff:=EXTdelaunayRed[i]-EXTdelaunayRed[j];
      eDist:=eDiff*GramMat*eDiff;
      DistMat[i][j]:=eDist;
      DistMat[j][i]:=eDist;
      if eDist=6 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  ListConn:=ConnectedComponents(GRA);
  for eConn in ListConn
  do
    if Length(eConn)<>3 then
      return false;
    fi;
    for eVert in eConn
    do
      if Length(Adjacency(GRA, eVert))<>2 then
        return false;
      fi;
    od;
  od;
  return true;
end;


GetStabilizer_A2pow12_Orbit:=function(EXTdelaunay)
  local EXTdelaunayRed, eIsoRed, ListDiffRed, ListSet, eVect, eProd, ListColl, pos, eSet, TheStab, ListStabGen, GRPret, FuncInsertGenerator, eGen, eList, nbOrbit, i, ListMatrGens, fGen, eBigMat, GRPmat;
  if Is_A2pow12_Orbit(EXTdelaunay)=false then
    Print("You are in wrong function, please turn back\n");
    Print(NullMat(5));
  fi;
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  eIsoRed:=Isobarycenter(EXTdelaunayRed);
  ListDiffRed:=List(EXTdelaunayRed, x->x-eIsoRed);
  ListSet:=[];
  for eVect in ListDiffRed
  do
    eProd:=eVect*GramMat;
    ListColl:=GetCollectedList(SHV, x->x*eProd);
    pos:=Position(ListColl.ListKeys, 2);
    eSet:=ListColl.ListOcc[pos];
    Add(ListSet, eSet);
  od;
  TheStab:=Stabilizer(SHV_PermGRP, ListSet[1], OnSets);
  ListStabGen:=[];
  GRPret:=Group(());
  FuncInsertGenerator:=function(eGen)
    if not(eGen in GRPret) then
      Add(ListStabGen, eGen);
      GRPret:=Group(ListStabGen);
    fi;
  end;
  for eGen in GeneratorsOfGroup(TheStab)
  do
    eList:=List(ListSet, x->Position(ListSet, OnSets(x, eGen)));
    FuncInsertGenerator(PermList(eList));
  od;
  for i in [2..36]
  do
    eGen:=RepresentativeAction(SHV_PermGRP, ListSet[1], ListSet[i], OnSets);
    eList:=List(ListSet, x->Position(ListSet, OnSets(x, eGen)));
    FuncInsertGenerator(PermList(eList));
    nbOrbit:=Length(Orbits(GRPret, [1..36], OnPoints));
    if nbOrbit=1 then
      ListMatrGens:=[];
      for fGen in ListStabGen
      do
        eBigMat:=__LemmaFindTransformation(EXTdelaunay, EXTdelaunay, fGen);
        Add(ListMatrGens, FuncExplodeBigMatrix(eBigMat).MatrixTransformation);
      od;
      GRPmat:=Group(ListMatrGens);
      SetSize(GRPmat, Order(GRPret));
      return GRPmat;
    fi;
  od;
  Print("We failed in our analysis\n");
  Print(NullMat(5));
end;


TestEquivalence_A2pow12_Orbit:=function(EXTdelaunay1, EXTdelaunay2)
  local EXTdelaunay1Red, EXTdelaunay2Red, eIso1Red, eIso2Red, ListDiff1Red, ListDiff2Red, ListSet1, ListSet2, eVect, eProd, ListColl, pos, eSet, eRepr, eList, ePerm, eBigMat;
  if Is_A2pow12_Orbit(EXTdelaunay1)=false or Is_A2pow12_Orbit(EXTdelaunay2)=false then
    Print("You are in wrong function, please turn back\n");
    Print(NullMat(5));
  fi;
  EXTdelaunay1Red:=List(EXTdelaunay1, x->x{[2..25]});
  EXTdelaunay2Red:=List(EXTdelaunay2, x->x{[2..25]});
  eIso1Red:=Isobarycenter(EXTdelaunay1Red);
  eIso2Red:=Isobarycenter(EXTdelaunay2Red);
  ListDiff1Red:=List(EXTdelaunay1Red, x->x-eIso1Red);
  ListDiff2Red:=List(EXTdelaunay2Red, x->x-eIso2Red);
  ListSet1:=[];
  for eVect in ListDiff1Red
  do
    eProd:=eVect*GramMat;
    ListColl:=GetCollectedList(SHV, x->x*eProd);
    pos:=Position(ListColl.ListKeys, 2);
    eSet:=ListColl.ListOcc[pos];
    Add(ListSet1, eSet);
  od;
  ListSet2:=[];
  for eVect in ListDiff2Red
  do
    eProd:=eVect*GramMat;
    ListColl:=GetCollectedList(SHV, x->x*eProd);
    pos:=Position(ListColl.ListKeys, 2);
    eSet:=ListColl.ListOcc[pos];
    Add(ListSet2, eSet);
  od;
  eRepr:=RepresentativeAction(SHV_PermGRP, ListSet1[1], ListSet2[1], OnSets);
  eList:=List(ListSet1, x->Position(ListSet2, OnSets(x, eRepr)));
  ePerm:=PermList(eList);
  eBigMat:=__LemmaFindTransformation(EXTdelaunay1, EXTdelaunay2, ePerm);
  if IsIntegralMat(eBigMat)=false then
    Print("There is a problem somewhere\n");
    Print(NullMat(5));
  fi;
  return eBigMat;
end;




Is_A1pow24_Orbit:=function(EXTdelaunay)
  local GRA, EXTdelaunayRed, i, j, eDiff, eDist, ListConn, SetSizes;
  if Length(EXTdelaunay)<>48 then
    return false;
  fi;
  GRA:=NullGraph(Group(()), 48);
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  for i in [1..47]
  do
    for j in [i+1..48]
    do
      eDiff:=EXTdelaunayRed[i]-EXTdelaunayRed[j];
      eDist:=eDiff*GramMat*eDiff;
      if eDist<>4 and eDist<>8 then
        return false;
      fi;
      if eDist=8 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  ListConn:=ConnectedComponents(GRA);
  SetSizes:=Set(List(ListConn, Length));
  if SetSizes<>[2] then
    return false;
  fi;
  return true;
end;



GetStabilizer_A1pow24_Orbit:=function(EXTdelaunay)
  local eCenter, EXTdelaunayRed, eCorresp, iEXT, eEXT, fEXT, pos, ListGens, TheGRP, FuncInsertGenerator, GRP, ListPermGen, O, ListDirections, i, eDir, TheCompl, ListPts, iVert, eDiff, SetPts, eRepr, eGen, eList, j, ePtOrig, h1, h2, h3, h4, h5, h6, h7, h8, ePtFinal, result, ListMatrGen, fGen, eBigMat, GRPmat;
  if Is_A1pow24_Orbit(EXTdelaunay)=false then
    Print("You called wrong function\n");
    Print(NullMat(5));
  fi;
  eCenter:=Isobarycenter(EXTdelaunay);
  EXTdelaunayRed:=List(EXTdelaunay, x->x{[2..25]});
  eCorresp:=[];
  for iEXT in [1..Length(EXTdelaunay)]
  do
    eEXT:=EXTdelaunay[iEXT];
    fEXT:=2*eCenter-eEXT;
    pos:=Position(EXTdelaunay, fEXT);
    Add(eCorresp, pos);
  od;
  ListGens:=[PermList(eCorresp)];
  TheGRP:=Group(ListGens);
  FuncInsertGenerator:=function(eGen)
    local nbOrbit;
    Print("Calling FuncInsertGenerator\n");
    if not(eGen in TheGRP) then
      Add(ListGens, eGen);
      TheGRP:=Group(ListGens);
      nbOrbit:=Length(Orbits(TheGRP, [1..48], OnPoints));
      Print("nbOrbit=", nbOrbit, "\n");
      if nbOrbit=1 then
        return "finished";
      else
        return "unfinished";
      fi;
    fi;
    return "unfinished";
  end;
  O:=Orbits(TheGRP, [1..48], OnPoints);
  ListDirections:=List(O, x->x[1]);
  for i in [1..24]
  do
    eDir:=ListDirections[i];
    TheCompl:=Difference([1..48], Set([eDir, eCorresp[eDir]]));
    ListPts:=[];
    for iVert in TheCompl
    do
      eDiff:=EXTdelaunayRed[iVert]-EXTdelaunayRed[eDir];
      Add(ListPts, Position(SHV, eDiff));
    od;
    SetPts:=Set(ListPts);
    eRepr:=RepresentativeAction(SHV_PermGRP, SetPts, ListOrbitEXT[224], OnSets);
    for eGen in GeneratorsOfGroup(ListContactStabilizers[224])
    do
      eList:=[];
      eList[eDir]:=eDir;
      eList[eCorresp[eDir]]:=eCorresp[eDir];
      for j in [1..Length(TheCompl)]
      do
        ePtOrig:=TheCompl[j];
        h1:=ListPts[j];
        h2:=OnPoints(h1, eRepr);
        h3:=Position(ListOrbitEXT[224], h2);
        h4:=OnPoints(h3, eGen);
        h5:=ListOrbitEXT[224][h4];
        h6:=OnPoints(h5, eRepr^(-1));
        h8:=Position(ListPts, h6);
        ePtFinal:=TheCompl[h8];
        eList[ePtOrig]:=ePtFinal;
      od;
      result:=FuncInsertGenerator(PermList(eList));
      if result="finished" then
        ListMatrGen:=[];
        for fGen in GeneratorsOfGroup(TheGRP)
        do
          eBigMat:=__LemmaFindTransformation(EXTdelaunay, EXTdelaunay, fGen);
          Add(ListMatrGen, FuncExplodeBigMatrix(eBigMat).MatrixTransformation);
        od;
        GRPmat:=Group(ListMatrGen);
        SetSize(GRPmat, Order(TheGRP));
        return GRPmat;
      fi;
    od;
  od;
  Print("Our Ansatz failed, please panic\n");
  Print(NullMat(5));
end;


TestEquivalence_A1pow24_Orbit:=function(EXTdelaunay1, EXTdelaunay2)
  local eCenter1, EXTdelaunay1Red, eCorresp1, iEXT, eEXT, fEXT, pos, eCenter2, EXTdelaunay2Red, eCorresp2, eDir, TheCompl1, TheCompl2, ListPts1, SetPts1, iVert, eDiff, ListPts2, SetPts2, eRepr, eList, i, h1, h2, h3, h4, h5, ePerm, eBigMat;
  if Is_A1pow24_Orbit(EXTdelaunay1)=false or Is_A1pow24_Orbit(EXTdelaunay2)=false then
    Print("You called wrong function\n");
    Print(NullMat(5));
  fi;
  eCenter1:=Isobarycenter(EXTdelaunay1);
  EXTdelaunay1Red:=List(EXTdelaunay1, x->x{[2..25]});
  eCorresp1:=[];
  for iEXT in [1..Length(EXTdelaunay1)]
  do
    eEXT:=EXTdelaunay1[iEXT];
    fEXT:=2*eCenter1-eEXT;
    pos:=Position(EXTdelaunay1, fEXT);
    Add(eCorresp1, pos);
  od;
  eCenter2:=Isobarycenter(EXTdelaunay2);
  EXTdelaunay2Red:=List(EXTdelaunay2, x->x{[2..25]});
  eCorresp2:=[];
  for iEXT in [1..Length(EXTdelaunay2)]
  do
    eEXT:=EXTdelaunay2[iEXT];
    fEXT:=2*eCenter2-eEXT;
    pos:=Position(EXTdelaunay2, fEXT);
    Add(eCorresp2, pos);
  od;
  eDir:=1;
  TheCompl1:=Difference([1..48], Set([eDir, eCorresp1[eDir]]));
  TheCompl2:=Difference([1..48], Set([eDir, eCorresp2[eDir]]));
  ListPts1:=[];
  for iVert in TheCompl1
  do
    eDiff:=EXTdelaunay1Red[iVert]-EXTdelaunay1Red[1];
    Add(ListPts1, Position(SHV, eDiff));
  od;
  SetPts1:=Set(ListPts1);
  ListPts2:=[];
  for iVert in TheCompl2
  do
    eDiff:=EXTdelaunay2Red[iVert]-EXTdelaunay2Red[1];
    Add(ListPts2, Position(SHV, eDiff));
  od;
  SetPts2:=Set(ListPts2);
  eRepr:=RepresentativeAction(SHV_PermGRP, SetPts1, SetPts2, OnSets);
  eList:=[];
  eList[eDir]:=eDir;
  eList[eCorresp1[eDir]]:=eCorresp2[eDir];
  for i in [1..46]
  do
    h1:=eCorresp1[i];
    h2:=ListPts1[i];
    h3:=OnPoints(h2, eRepr);
    h4:=Position(ListPts2, h3);
    h5:=eCorresp2[h4];
    eList[h1]:=h4;
  od;
  ePerm:=PermList(eList);
  eBigMat:=__LemmaFindTransformation(EXTdelaunay1, EXTdelaunay2, ePerm);
  if IsIntegralMat(eBigMat)=false then
    Print("There is a problem somewhere\n");
    Print(NullMat(5));
  fi;
  return eBigMat;
end;



LeechDelaunayStabilizer:=function(DataLattice, EXTdelaunay)
  local TheReply, DM, CP, TheCenter, GRP, REP, EasyCase, HLR;
  DM:=DistanceMatrixDelaunay(DataLattice.GramMat, EXTdelaunay);
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXTdelaunay);
  TheCenter:=CP.Center;
  GRP:=AutomorphismGroupEdgeColoredGraph(DM);
  if Is_A1pow24_Orbit(EXTdelaunay)=true then
    TheReply:=GetStabilizer_A1pow24_Orbit(EXTdelaunay);
    EasyCase:=false;
  elif Is_a1pow25_Orbit(EXTdelaunay)=true then
    TheReply:=GetStabilizer_a1pow25_Orbit(EXTdelaunay);
    EasyCase:=false;
  elif Is_A2pow12_Orbit(EXTdelaunay)=true then
    TheReply:=GetStabilizer_A2pow12_Orbit(EXTdelaunay);
    EasyCase:=false;
  else
    REP:=Stabilizer_Method0(DataLattice, EXTdelaunay, GRP);
    if REP<>fail then
      EasyCase:=true;
      TheReply:=REP;
    else
      EasyCase:=false;
      if Order(GRP) < 70000 then
        TheReply:=Stabilizer_Method4(DataLattice, EXTdelaunay, GRP);
      else
        TheReply:=Stabilizer_Method6(DataLattice, EXTdelaunay, TheCenter);
      fi;
    fi;
  fi;
  HLR:=VertexRepresentationDelaunaySymmetry(TheReply, EXTdelaunay, TheCenter);
  return rec(PrivateInfo:=rec(EasyCase:=EasyCase, GRP:=GRP), 
             PermutationStabilizer:=HLR.PermutationStabilizer,
             PhiPermMat:=HLR.PhiPermMat);
end;



LeechDelaunayTestEquivalence:=function(DataLattice, EXTdelaunay1, EXTdelaunay2, Delaunay1Stab)
  local CP1, CP2, TheCenter1, TheCenter2, DM1, DM2, test, ePerm, GRP1, REP, eEquiv;
  Print("Entering TestEquivalenceOfDelaunayHighDimMethod6\n");
  #
  CP1:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXTdelaunay1);
  CP2:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXTdelaunay2);
  TheCenter1:=CP1.Center;
  TheCenter2:=CP2.Center;
  if Is_A1pow24_Orbit(EXTdelaunay1)=true then
    if Is_A1pow24_Orbit(EXTdelaunay2)=false then
      return false;
    fi;
    eEquiv:=TestEquivalence_A1pow24_Orbit(EXTdelaunay1, EXTdelaunay2);
  elif Is_a1pow25_Orbit(EXTdelaunay1)=true then
    if Is_a1pow25_Orbit(EXTdelaunay2)=false then
      return false;
    fi;
    eEquiv:=TestEquivalence_a1pow25_Orbit(EXTdelaunay1, EXTdelaunay2);
  elif Is_A2pow12_Orbit(EXTdelaunay1)=true then
    if Is_A2pow12_Orbit(EXTdelaunay2)=false then
      return false;
    fi;
    eEquiv:=TestEquivalence_A2pow12_Orbit(EXTdelaunay1, EXTdelaunay2);
  else
    DM1:=DistanceMatrixDelaunay(DataLattice.GramMat, EXTdelaunay1);
    DM2:=DistanceMatrixDelaunay(DataLattice.GramMat, EXTdelaunay2);
    test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
    if test=false then
      return false;
    fi;
    ePerm:=PermList(test);
    GRP1:=Delaunay1Stab.PrivateInfo.GRP;
    REP:=Equivalence_Method0(DataLattice, EXTdelaunay1, EXTdelaunay2, Delaunay1Stab, ePerm);
    if REP<>fail then
      eEquiv:=REP;
    else
      if Order(GRP1)<=70000 then
        eEquiv:=Equivalence_Method4(DataLattice, EXTdelaunay1, EXTdelaunay2, GRP1, ePerm);
      else
        eEquiv:=Equivalence_Method6(DataLattice, EXTdelaunay1, EXTdelaunay2, TheCenter1, TheCenter2);
      fi;
    fi;
  fi;
  if eEquiv=false then
    return false;
  fi;
  if IsIntegralMat(eEquiv)=false then
    Print("We have the wrong matrix\n");
    Print(NullMat(5));
  fi;
  if TheCenter1*eEquiv<>TheCenter2 then
    Print("We have a big problem in that place, please debug\n");
    Print(NullMat(5));
  fi;
  return eEquiv;
end;









MyOption:="";
FuncLatticeAutomorphism:=function(ListMat, SVR, AffBas)
  return ArithmeticAutomorphismMatrixFamily_Nauty(ListMat, SVR);
end;
FuncLatticeIsomorphism:=function(ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2)
  return ArithmeticEquivalenceMatrixFamily_Nauty(ListMat1, SVR1, ListMat2, SVR2);
end;

DataLattice:=rec(TestBelonging:=IsIntegralMat, n:=24, 
                 InvariantBase:=SHV, NeedAffBas:=false, 
                 FuncLatticeAutomorphism:=FuncLatticeAutomorphism, 
                 FuncLatticeIsomorphism:=FuncLatticeIsomorphism,
                 AffBas:="irrel", 
                 GramMat:=GramMat);


FuncIsomorphy:=function(EXT1, EXT2)
  local DM1, GRP1, TheStabMat, Delaunay1Stab, EasyCase, TheEquiv, eList;
  DM1:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT1);
  GRP1:=AutomorphismGroupEdgeColoredGraph(DM1);
  TheStabMat:=Stabilizer_Method0(DataLattice, EXT1, GRP1);
  if TheStabMat=fail then
    EasyCase:=false;
  else
    EasyCase:=true;
  fi;
  Delaunay1Stab:=rec(PrivateInfo:=rec(EasyCase:=EasyCase, GRP:=GRP1));
  TheEquiv:=LeechDelaunayTestEquivalence(DataLattice, EXT1, EXT2, Delaunay1Stab);
  if TheEquiv=false then
    return false;
  else
    eList:=List(EXT1, x->Position(EXT2, x*TheEquiv));
    return PermList(eList);
  fi;
end;

#EXTdelaunay227:=ListInformationsPrev[227].EXTnearest;
#TheStab:=LeechDelaunayStabilizer(DataLattice, EXTdelaunay227);
#Print(NullMat(5));

FileDelaunayStabilizer:="Database/DelaunayStabilizers";
if IsExistingFilePlusTouch(FileDelaunayStabilizer)=false then
  ListDelaunayStabilizers:=[];
  for iOrbit in [1..Length(ListInformationsPrev)]
  do
    if ListInformationsPrev[iOrbit].DelaunayStatus<>"It is something else" then
      EXTdelaunay:=ListInformationsPrev[iOrbit].EXTnearest;
      TheStab:=LeechDelaunayStabilizer(DataLattice, EXTdelaunay);
      Add(ListDelaunayStabilizers, TheStab.PermutationStabilizer);
    else
      Add(ListDelaunayStabilizers, "irrelevant");
    fi;
    Print("Delaunay stabilizer of orbit ", iOrbit, " done\n");
  od;
  SaveDataToFilePlusTouch(FileDelaunayStabilizer, ListDelaunayStabilizers);
else
  ListDelaunayStabilizers:=ReadAsFunction(FileDelaunayStabilizer)();
fi;

FileDelaunayEquivalences:="Database/DelaunayEquivalences";
if IsExistingFilePlusTouch(FileDelaunayEquivalences)=false then
  ListDelaunayEquivalences:=[];
  ListStatus:=ListWithIdenticalEntries(Length(ListDelaunay), 1);
  for iIter in [1..Length(ListDelaunay)]
  do
    iOrbit:=ListDelaunay[iIter];
    if ListStatus[iIter]=1 then
      Print("Treating iOrbit=", iOrbit, "\n");
      EXTdelaunay1:=ListInformationsPrev[iOrbit].EXTnearest;
      TheClass:=[iOrbit];
      for jIter in [iIter+1..Length(ListDelaunay)]
      do
        jOrbit:=ListDelaunay[jIter];
        if ListStatus[jIter]=1 then
          Print("  testing for jOrbit=", jOrbit, "\n");
          EXTdelaunay2:=ListInformationsPrev[jOrbit].EXTnearest;
          eEquiv:=FuncIsomorphy(EXTdelaunay1, EXTdelaunay2);
          if eEquiv<>false then
            Add(TheClass, jOrbit);
            ListStatus[jIter]:=0;
          fi;
        fi;
      od;
      Add(ListDelaunayEquivalences, TheClass);
      ListStatus[iIter]:=0;
    fi;
  od;
  SaveDataToFilePlusTouch(FileDelaunayEquivalences, ListDelaunayEquivalences);
else
  ListDelaunayEquivalences:=ReadAsFunction(FileDelaunayEquivalences)();
fi;



ListNumberBelonging:=ListWithIdenticalEntries(Length(ListOrbitEXT), 0);
ListNumberBelonging{ListNotDelaunay}:=ListWithIdenticalEntries(Length(ListNotDelaunay), 1000000);
ListIdxClasses:=ListWithIdenticalEntries(Length(ListOrbitEXT), 0);
ListIdxClasses{ListNotDelaunay}:=ListWithIdenticalEntries(Length(ListNotDelaunay), 1000000);


for iClass in [1..Length(ListDelaunayEquivalences)]
do
  eClass:=ListDelaunayEquivalences[iClass];
  for iVert in eClass
  do
    ListNumberBelonging[iVert]:=Length(eClass);
    ListIdxClasses[iVert]:=iClass;
  od;
od;



ListIncidence:=List(ListOrbitEXT, Length);
ListStabOrder:=List(ListContactStabilizers, Order);
ListSqrDist:=List(ListInformationsPrev, x->x.Sqr2);
DiscriminantList:=List([1..Length(ListOrbitEXT)],
x->[
    1/ListSqrDist[x],
    1/ListNumberBelonging[iVert], 
    ListIdxClasses[x], 
    1/ListIncidence[x],
    ListStabOrder[x]
]);

eReordPerm:=SortingPerm(DiscriminantList);
ReordListInformations:=Permuted(ListInformationsPrev, eReordPerm);
ReordDiscriminantList:=Permuted(DiscriminantList, eReordPerm);

ReordListOrbitEXT:=Permuted(ListOrbitEXT, eReordPerm);
ReordListContactStabilizers:=Permuted(ListContactStabilizers, eReordPerm);

ReordListDelaunay:=OnSets(ListDelaunay, eReordPerm);
ReordListNotDelaunay:=OnSets(ListNotDelaunay, eReordPerm);

ReordListDelaunayEquivalences:=List(ListDelaunayEquivalences, x->OnSets(x, eReordPerm));
ReordListDelaunayStabilizers:=Permuted(ListDelaunayStabilizers, eReordPerm);


ListSizes:=ListWithIdenticalEntries(24, 0);
FullMat:=[];
for iOrbit in [1..Length(ReordListNotDelaunay)]
do
  iOrbitIdx:=ReordListDelaunay[iOrbit];
  eCenterRed:=ReordListInformations[iOrbitIdx].eCenterRed;
  eInfo:=RemoveFractionPlusCoef(eCenterRed);
  Add(FullMat, eInfo.TheVect);
  for iCol in [1..24]
  do
    eStr:=String(eInfo.TheVect[iCol]);
    ListSizes[iCol]:=Maximum(ListSizes[iCol], Length(eStr));
  od;
od;
ListSizesRed:=ListWithIdenticalEntries(12, 0);
for i in [1..12]
do
  ListSizesRed[i]:=Maximum(ListSizes[i], ListSizes[i+12]);
od;

DecimalStringFromHalfInt:=function(eVal)
  local H;
  if IsInt(eVal)=true then
    return String(eVal);
  fi;
  if eVal<0 then
    return Concatenation("-", DecimalStringFromHalfInt(-eVal));
  fi;
  H:=eVal-1/2;
  return Concatenation(String(H), ".5");
end;


FileNotDelaunay:="LatexFiles/TEX_ListNotDelaunay";
RemoveFileIfExist(FileNotDelaunay);
output:=OutputTextFile(FileNotDelaunay, true);
AppendTo(output, "\\begin{equation*}\n");
AppendTo(output, "\\textrm{\\begin{tiny}\n");
AppendTo(output, "\\begin{tabular}{|c|c|c|c|");
AppendTo(output, "p{4.6mm}");
for i in [2..12]
do
  if ListSizesRed[i]=3 then
    AppendTo(output, "p{2.4mm}");
  else
    AppendTo(output, "p{3.0mm}");
  fi;
od;
AppendTo(output, "|}\n");
AppendTo(output, "\\hline\n");
AppendTo(output, "\$r^2\$ & Inc & \$|Stab|\$ & d");
for iCol in [1..12]
do
  AppendTo(output, " & ");
od;
GetPrevLen:=function(eVal)
  local nb, nbChar;
  if eVal<0 then
#    nb:=3/2;
    nb:=2;
  else
    nb:=0;
  fi;
  nbChar:=Length(String(eVal));
  return 2*nbChar+nb;
end;



FileCoordinateVertices:="Database/COORD_VerticesNotDelaunay";
RemoveFileIfExist(FileCoordinateVertices);
outputVert:=OutputTextFile(FileCoordinateVertices, true);

AppendTo(output, "\\\\\\hline\n");
for iOrbit in [1..Length(ReordListNotDelaunay)]
do
  iOrbitIdx:=ReordListNotDelaunay[iOrbit];
  rSqr:=ReordListInformations[iOrbitIdx].Sqr2;
  eInc:=ReordListOrbitEXT[iOrbitIdx];
  eStab:=ReordListContactStabilizers[iOrbitIdx];
  eCenterRed:=ReordListInformations[iOrbitIdx].eCenterRed;
  WriteVector(outputVert, eCenterRed);
  eInfo:=RemoveFractionPlusCoef(eCenterRed);
  AppendTo(output, rSqr, " & ", Length(eInc), " & ", Order(eStab), " & ", 1/eInfo.TheMult);
  for iCol in [1..12]
  do
    AppendTo(output, " & ");
    eVal:=eInfo.TheVect[iCol];
    eStr:=String(eVal);
    nb:=-GetPrevLen(eVal);
    if iCol=1 then
      nb:=nb+4;
    fi;
    AppendTo(output, "{\\hskip ", DecimalStringFromHalfInt(nb), "pt} ");
    AppendTo(output, "\$", eStr, "\$");
  od;
  AppendTo(output, "\\\\\n");
  #
  AppendTo(output, " & & &");
  for iCol in [1..12]
  do
    AppendTo(output, " & ");
    eVal:=eInfo.TheVect[iCol+12];
    eStr:=String(eVal);
    nb:=-GetPrevLen(eVal);
    if iCol=1 then
      nb:=nb+4;
    fi;
    AppendTo(output, "{\\hskip ", DecimalStringFromHalfInt(nb), "pt} ");
    AppendTo(output, "\$", eStr, "\$");
  od;
  AppendTo(output, "\\\\\n");
od;
AppendTo(output, "\\hline\n");
AppendTo(output, "\\end{tabular}\n");
AppendTo(output, "\\end{tiny}}\n");
AppendTo(output, "\\end{equation*}\n");
CloseStream(output);
CloseStream(outputVert);
FinalFileTex:="LatexFiles/NotDelaunay.tex";
FinalFileDVI:="LatexFiles/NotDelaunay.dvi";
RemoveFileIfExist(FinalFileTex);
RemoveFileIfExist(FinalFileDVI);
Exec("cat Header.tex ", FileNotDelaunay, " Footer.tex > ", FinalFileTex);
Exec("latex ", FinalFileTex);
Exec("dvips ", FinalFileDVI, " -o");







FileDelaunay:="LatexFiles/TEX_ListDelaunay";
RemoveFileIfExist(FileDelaunay);
output:=OutputTextFile(FileDelaunay, true);
AppendTo(output, "\\begin{center}\n");
AppendTo(output, "\\begin{tabular}{|c|c|c|c|c|c|}\n");
AppendTo(output, "\\hline\n");
AppendTo(output, "\$r^2\$ & \$|\vert(D)|\$ & Coxeter diagram & \$|\Stab(D)|\$ & \$|\Stab(v)|\$ & Inc\\\\\n");
AppendTo(output, "\\hline\n");
eDiscPrev:=[0,0,0,0,0];
for iOrbit in [1..Length(ReordListDelaunay)]
do
  iOrbitIdx:=ReordListDelaunay[iOrbit];
  eDisc:=ReordDiscriminantList[iOrbitIdx];
  rSqr:=ReordListInformations[iOrbitIdx].Sqr2;
  rBorcherds:=ReordListInformations[iOrbitIdx].TheSymbolTotalDelaunay;
  eIncidence:=Length(ReordListOrbitEXT[iOrbitIdx]);
  nbV:=Length(ReordListInformations[iOrbitIdx].EXTnearest);
  DelaunayStab:=ReordListDelaunayStabilizers[iOrbitIdx];
  ordDelStab:=Order(DelaunayStab);
  ordStabContact:=Order(ReordListContactStabilizers[iOrbitIdx]);
  if eDiscPrev[3]<>eDisc[3] then
    AppendTo(output, rSqr, " & ", nbV, " & \$", rBorcherds, "\$ & ", ordDelStab);
  else
    AppendTo(output,       " &           &                  & ");
  fi;
  AppendTo(output, " & ", ordStabContact, " & ", eIncidence, "\\\\\n");
  eDiscPrev:=eDisc;
od;
AppendTo(output, "\\hline\n");
AppendTo(output, "\\end{tabular}\n");
AppendTo(output, "\\end{center}\n");
CloseStream(output);
FinalFileTex:="LatexFiles/VERT_Delaunay.tex";
FinalFileDVI:="LatexFiles/VERT_Delaunay.dvi";
RemoveFileIfExist(FinalFileTex);
RemoveFileIfExist(FinalFileDVI);
Exec("cat Header.tex ", FileDelaunay, " Footer.tex > ", FinalFileTex);
Exec("latex ", FinalFileTex);
Exec("dvips ", FinalFileDVI, " -o");




FileGramMat:="LatexFiles/TEX_TheGramMat";
n:=Length(GramMat);
RemoveFileIfExist(FileGramMat);
output:=OutputTextFile(FileGramMat, true);
AppendTo(output, "\\begin{equation*}\n");
AppendTo(output, "\\left(\\textrm{\\begin{tiny}\n");
AppendTo(output, "\\begin{tabular}{");
for i in [1..n]
do
  AppendTo(output, "c");
od;
AppendTo(output, "}\n");
for i in [1..n]
do
  for j in [1..n]
  do
    if j>1 then
      AppendTo(output, " & ");
    fi;
    eStr:=String(GramMat[i][j]);
    if Length(eStr)=3 then
      AppendTo(output, "{\\hskip -13pt} ");
    else
      if Length(eStr)=2 then
        AppendTo(output, "{\\hskip -9pt} ");
      fi;
    fi;
    AppendTo(output, "\$", eStr, "\$");
  od;
  if i < n then
    AppendTo(output, "\\\\");
  fi;
  AppendTo(output, "\n");
od;
AppendTo(output, "\\end{tabular}\n");
AppendTo(output, "\\end{tiny}}\\right)\n");
AppendTo(output, "\\end{equation*}\n");
CloseStream(output);
FinalFileTex:="LatexFiles/GramMat.tex";
FinalFileDVI:="LatexFiles/GramMat.dvi";
RemoveFileIfExist(FinalFileTex);
RemoveFileIfExist(FinalFileDVI);
Exec("cat Header.tex ", FileGramMat, " Footer.tex > ", FinalFileTex);
Exec("latex ", FinalFileTex);
Exec("dvips ", FinalFileDVI, " -o");
