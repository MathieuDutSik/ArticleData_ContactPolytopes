GramMat:=ReadAsFunction("GramMat")();
n:=Length(GramMat);

GRP:=ReadAsFunction("LeechGroup")();
SHV:=ReadAsFunction("LeechNeigh")();

ListPermGen:=GetListPermGens(SHV, GeneratorsOfGroup(GRP));
PermGRP:=Group(ListPermGen);
SetSize(PermGRP, Order(GRP));

ListPermGenAntipodal:=[];
nbAnti:=Length(SHV)/2;
for eGen in ListPermGen
do
  eList:=[];
  for iAnti in [1..nbAnti]
  do
    i:=2*iAnti-1;
    j:=OnPoints(i, eGen);
    if j mod 2=0 then
      jAnti:=j/2;
    else
      jAnti:=(j+1)/2;
    fi;
    Add(eList, jAnti);
  od;
  Add(ListPermGenAntipodal, PermList(eList));
od;
PermGRPantipodal:=Group(ListPermGenAntipodal);
phiMapping:=GroupHomomorphismByImagesNC(PermGRP, PermGRPantipodal, ListPermGen, ListPermGenAntipodal);

SetToAntipodal:=function(eSet)
  local eSetAnti, i, iAnti;
  eSetAnti:=[];
  for i in eSet
  do
    if i mod 2=0 then
      iAnti:=i/2;
    else
      iAnti:=(i+1)/2;
    fi;
    Add(eSetAnti, iAnti);
  od;
  if Length(Set(eSetAnti))< Length(eSetAnti) then
    Print("The algorithm is not going to work, go back to black board\n");
    Print(NullMat(5));
  fi;
  return eSetAnti;
end;

TestEquivalenceAntipodalMethod:=function(eSet1, eSet2)
  local eSetAnti1, eSetAnti2, gAnti, g, eSet1image, GRPanti, GRP, g2;
  eSetAnti1:=SetToAntipodal(eSet1);
  eSetAnti2:=SetToAntipodal(eSet2);
  Print("Before first RepresentativeAction\n");
  gAnti:=RepresentativeAction(PermGRPantipodal, eSetAnti1, eSetAnti2, OnSets);
  Print(" After first RepresentativeAction\n");
  if gAnti=fail then
    return fail;
  fi;
  Print("Before PreImagesRepresentative\n");
  g:=PreImagesRepresentative(phiMapping, gAnti);
  Print(" After PreImagesRepresentative\n");
  eSet1image:=OnSets(eSet1, g);
  Print("Before Stabilizer\n");
  GRPanti:=Stabilizer(PermGRPantipodal, eSetAnti2, OnSets);
  Print(" After Stabilizer\n");
  Print("Before PreImage\n");
  GRP:=PreImage(phiMapping, GRPanti);
  Print(" After PreImage\n");
  Print("Before second RepresentativeAction\n");
  g2:=RepresentativeAction(GRP, eSet1image, eSet2, OnSets);
  Print(" After second RepresentativeAction\n");
  if g2=fail then
    return fail;
  fi;
  return g*g2;
end;
StabilizerAntipodalMethod:=function(eSet)
  local eSetAnti, TheStabAnti, TheStab;
  eSetAnti:=SetToAntipodal(eSet);
  TheStabAnti:=Stabilizer(PermGRPantipodal, eSetAnti, OnSets);
  Print("|TheStabAnti|=", Order(TheStabAnti), "\n");
  TheStab:=PreImage(phiMapping, TheStabAnti);
  Print("|TheStab|=", Order(TheStab), "\n");
  return Stabilizer(TheStab, eSet, OnSets);
end;

IsCorrectDistMat:=function(ListInc)
  local DistMat, nbVert, i, j, Scal;
  nbVert:=Length(ListInc);
  DistMat:=NullMat(nbVert, nbVert);
  for i in [1..nbVert]
  do
    for j in [i..nbVert]
    do
      Scal:=SHV[ListInc[i]]*GramMat*SHV[ListInc[j]];
      if i<>j then
        if Scal<>2 then
          return false;
        fi;
      else
        if Scal<>4 then
          Print("Please really PANIC hard!!!!\n");
          Print(NullMat(5));
        fi;
      fi;
    od;
  od;
  return true;
end;




GetAllInfos:=function(ListInc)
  local ListVert, idx, eVert, TheFinal, EXTdelaunay, eCenter1, eCenter2, eCenterChar, ThePair, SVR, TheAffBasis, i;
  ListVert:=[];
  for idx in ListInc
  do
    eVert:=Concatenation([1], SHV[idx]);
    Add(ListVert, eVert);
  od;
  TheFinal:=ListWithIdenticalEntries(25,0);
  TheFinal[1]:=1;
  EXTdelaunay:=Concatenation(ListVert, [TheFinal]);
  eCenter1:=Isobarycenter(ListVert);
  eCenter2:=Isobarycenter(EXTdelaunay);
  eCenterChar:=(eCenter1+eCenter2)/2;
  ThePair:=CharacterizingPair(GramMat, eCenterChar);
  SVR:=List(SHV, x->Concatenation([0], x));
  Append(SVR, EXTdelaunay);
  Append(SVR, -EXTdelaunay);
  TheAffBasis:=[];
  for i in [1..24]
  do
    eVert:=ListWithIdenticalEntries(25,0);
    eVert[i+1]:=1;
    Add(TheAffBasis, eVert);
  od;
  Add(TheAffBasis, EXTdelaunay[1]);
  return rec(ThePair:=ThePair, TheAffBasis:=TheAffBasis, SVR:=SVR);
end;

StabilizerDelaunayMethod:=function(ListInc)
  local AllInfos, TheGRP, ListSmallGens, eMat, sSmallMat, ListPermGen, eGen, RetGRP, eSmallMat;
  if IsCorrectDistMat(ListInc)=false then
    Print("We should never have been here\n");
    Print(NullMat(5));
  fi;
  AllInfos:=GetAllInfos(ListInc);
  TheGRP:=ArithmeticAutomorphismMatrixFamily_HackSouvignier("", AllInfos.ThePair, AllInfos.SVR, AllInfos.TheAffBasis);
  ListSmallGens:=[];
  for eMat in GeneratorsOfGroup(TheGRP)
  do
    eSmallMat:=FuncExplodeBigMatrix(eMat).MatrixTransformation;
    if eMat[1][1]=1 then
      Add(ListSmallGens, eSmallMat);
    else
      Add(ListSmallGens, -eSmallMat);
    fi;
  od;
  ListPermGen:=GetListPermGens(SHV, ListSmallGens);
  for eGen in ListPermGen
  do
    if OnSets(ListInc, eGen)<>ListInc then
      Print("This is incorrect, please correct\n");
      Print(NullMat(5));
    fi;
  od;
  RetGRP:=Group(ListPermGen);
  SetSize(RetGRP, Order(TheGRP)/2);
  return RetGRP;
end;



TestEquivalenceDelaunayMethod:=function(ListInc1, ListInc2)
  local AllInfos1, AllInfos2, TheTest, WorkMat, eMat, ListPerm, eRetPerm;
  if IsCorrectDistMat(ListInc1)=false or IsCorrectDistMat(ListInc1)=false then
    Print("We should never have been here\n");
    Print(NullMat(5));
  fi;
  AllInfos1:=GetAllInfos(ListInc1);
  AllInfos2:=GetAllInfos(ListInc2);
  TheTest:=ArithmeticEquivalenceMatrixFamily_HackSouvignier("", AllInfos1.ThePair, AllInfos1.SVR, AllInfos1.TheAffBasis, AllInfos2.ThePair, AllInfos2.SVR, AllInfos2.TheAffBasis);
  if TheTest=false then
    return false;
  fi;
  if TheTest[1][1]=-1 then
    WorkMat:=-TheTest;
  else
    WorkMat:=TheTest;
  fi;
  eMat:=FuncExplodeBigMatrix(WorkMat).MatrixTransformation;
  ListPerm:=GetListPermGens(SHV, [eMat]);
  eRetPerm:=ListPerm[1];
  if OnSets(ListInc1, eRetPerm)<>ListInc2 then
    Print("This is incorrect, please correct\n");
    Print(NullMat(5));
  fi;
  return eRetPerm;
end;





MyFuncInvariant:=function(eSet)
  local nbV, RetS, GetListDist, TheDistMat, i, j, eDiff, TheDist, ListDistInvariant;
  nbV:=Length(eSet);
  if nbV>55 then
    RetS:=2;
  else
    if nbV>30 then
      RetS:=3;
    else
      RetS:=4;
    fi;
  fi;
  GetListDist:=function(SelectSet)
    local ListDist, TheSiz, i, j;
    ListDist:=[];
    TheSiz:=Length(SelectSet);
    for i in [1..TheSiz-1]
    do
      for j in [i+1..TheSiz]
      do
        Add(ListDist, SHV[SelectSet[i]]*GramMat*SHV[SelectSet[j]]);
      od;
    od;
    return Collected(ListDist);
  end;
  TheDistMat:=NullMat(nbV, nbV);
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      eDiff:=SHV[eSet[i]]-SHV[eSet[j]];
      TheDist:=eDiff*GramMat*eDiff;
      TheDistMat[i][j]:=TheDist;
      TheDistMat[j][i]:=TheDist;
    od;
  od;
  ListDistInvariant:=List(Combinations(eSet, RetS), GetListDist);
  return rec(OrdGrp:=Order(AutomorphismGroupEdgeColoredGraph(TheDistMat)), DistInvariant:=Collected(ListDistInvariant));
end;







FAC:=List(SHV, x->Concatenation(-x*GramMat, [1]));
Print("FAC has been constructed\n");
FuncDistMat:=function(FACask)
  local ListInc, DistMat, nbVert, i, j, Scal;
  ListInc:=List(FACask, x->Position(FAC, x));
  nbVert:=Length(ListInc);
  DistMat:=NullMat(nbVert, nbVert);
  for i in [1..nbVert]
  do
    for j in [i..nbVert]
    do
      Scal:=SHV[ListInc[i]]*GramMat*SHV[ListInc[j]];
      if i<>j then
        DistMat[i][j]:=Scal;
        DistMat[j][i]:=Scal;
      else
        DistMat[i][j]:=Scal;
      fi;
    od;
  od;
  return DistMat;
end;
FuncStabilizer:=function(FACask)
  if Length(FACask)=196560 then
    return PermGRP;
  fi;
  if Length(FACask)=46 then
    return Group(());
  fi;
  if Length(FACask)=24 then
    return Group(());
  fi;
  return AutomorphismGroupEdgeColoredGraph(FuncDistMat(FACask));
end;
FuncIsomorphy:=function(FAC1, FAC2)
  local DistMat1, DistMat2, test;
  DistMat1:=FuncDistMat(FAC1);
  DistMat2:=FuncDistMat(FAC2);
  test:=IsIsomorphicEdgeColoredGraph(DistMat1, DistMat2);
  if test=false then
    return false;
  else
    return PermList(test);
  fi;
end;
FuncInvariant:=function(EXT)
  return [Length(EXT), RankMat(EXT)];
end;


GetRay6:=function()
  local ListScal, SetScal, ListSumVect, ListNorm, ListNB, eScal, ThePos, TheSumVect, TheNorm, TheNB, Pos, TheVect6, ListScal6, SetScal6, ListNB6, SelectScal, Set552;
  ListScal:=List(SHV, x->x*GramMat*SHV[1]);
  SetScal:=Set(ListScal);
  ListSumVect:=[];
  ListNorm:=[];
  ListNB:=[];
  for eScal in SetScal
  do
    ThePos:=Position(ListScal, eScal);
    TheSumVect:=SHV[1]+SHV[ThePos];
    TheNorm:=TheSumVect*GramMat*TheSumVect;
    TheNB:=Length(Filtered(ListScal, x->x=eScal));
    Add(ListSumVect, TheSumVect);
    Add(ListNorm, TheNorm);
    Add(ListNB, TheNB);
  od;
  Pos:=Position(ListNorm, 6);
  TheVect6:=ListSumVect[Pos];
  #
  ListScal6:=List(SHV, x->x*GramMat*TheVect6);
  SetScal6:=Set(ListScal6);
  ListNB6:=List(SetScal6, x->Length(Filtered(ListScal6, y->y=x)));
  Pos:=Position(ListNB6, 552);
  SelectScal:=SetScal6[Pos];
  Set552:=Filtered([1..Length(ListScal6)], x->ListScal6[x]=SelectScal);
#  TheStab:=Stabilizer(PermGRP, Set552, OnSets);
  return [Set552];
end;



GetInitialRays:=function(EXT, nb)
  if Length(EXT)=196560 then
    return GetRay6();
  else
    return GetRAYS(EXT, nb);
  fi;
end;




IsRespawn:=function(OrdGRP, EXT, TheDepth)
  local nbInc;
  nbInc:=Length(EXT);
  if nbInc <= 40 then
    return false;
  fi;
  if OrdGRP >= 252000 then
    return true;
  fi;
  if TheDepth>=3 then
    return false;
  fi;
  if OrdGRP >= 4000 then
    return true;
  fi;
  return false;
end;


IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
  if TheDepth=0 then
    return false;
  fi;
  if EllapsedTime>=600 then
    return true;
  fi;
  if Length(EXT)<=27 then
    return false;
  fi;
  return true;
end;
ThePathWork:="./TheWork/";
Exec("mkdir -p ", ThePathWork);
ThePath:=Concatenation(ThePathWork, "tmp/");
Exec("mkdir -p ", ThePath);
PathSave:=Concatenation(ThePathWork, "PathSAVE/");
Exec("mkdir -p ", PathSave);


IsItRegularSimplex:=function(TheInc)
  local nbPt, iVert, jVert, TheScal;
  nbPt:=Length(TheInc);
  for iVert in [1..nbPt-1]
  do
    for jVert in [iVert+1..nbPt]
    do
      TheScal:=SHV[TheInc[iVert]]*GramMat*SHV[TheInc[jVert]];
      if TheScal<>2 then
        return false;
      fi;
    od;
  od;
  return true;
end;

#
# For isomorphy tests in the ADM, we can choose a different
# group formalism. This can help speed up performance.
# see below the standard PermutationGroup + OnSets formalism
MyPersoOnSetsGroupFormalism:=function()
  local __LiftingOrbits, OnSetsRepresentativeAction, OnSetsStabilizer, GroupUnion, ToPermGroup, TheOrder, OnSetsIsSubgroup, OnSetsGroupConjugacy, OnSetsTransformIncidenceList, MyOrbitGroupFormalism, BankKeyInformation, BankCompleteInformation, BankGetVertexSet, BankGetGroup, BankGetForIsom, BankGetListObject;

  __LiftingOrbits:=function(EXT, ListInc, SmallGroup, BigGroup)
    local NewListInc, eInc;
    NewListInc:=[];
    Print("|SmallGroup|=", Order(SmallGroup), "  |BigGroup|=", Order(BigGroup), "\n");
    for eInc in ListInc
    do
      Append(NewListInc, __IndividualLifting(eInc, SmallGroup, BigGroup));
    od;
    return NewListInc;
  end;
  OnSetsStabilizer:=function(EXT, GRP, eInc)
    if Order(GRP)=8315553613086720000 then
#      return SecondReduceGroupAction(StabilizerAntipodalMethod(eInc));
      return SecondReduceGroupAction(Stabilizer(GRP, eInc, OnSets), eInc);
    else
      return SecondReduceGroupAction(Stabilizer(GRP, eInc, OnSets), eInc);
    fi;
  end;
  GroupUnion:=function(Grp1, Grp2)
    return Group(SmallGeneratingSet(Group(Union(GeneratorsOfGroup(Grp1), GeneratorsOfGroup(Grp2)))));
  end;
  ToPermGroup:=function(EXT, Grp)
    return Grp;
  end;
  TheOrder:=function(GRP)
    return Order(GRP);
  end;
  OnSetsIsSubgroup:=function(GRP1, GRP2)
    return IsSubgroup(GRP1, GRP2);
  end;
  OnSetsGroupConjugacy:=function(GRP, eElt)
    local NewGens, eGen;
    NewGens:=[];
    for eGen in GeneratorsOfGroup(GRP)
    do
      Add(NewGens, eElt^(-1)*eGen*eElt);
    od;
    return PersoGroupPerm(NewGens);
  end;
  OnSetsTransformIncidenceList:=function(ListEXT1, ListEXT2, TheEquiv, ListListInc)
    return List(ListListInc, x->OnSets(x, TheEquiv));
  end;
  MyOrbitGroupFormalism:=function(EXT, TheGroup, Prefix, SavingTrigger)
    local FuncInvariant, FuncIsomorphy, FuncInvariantUpdate, OrderLincStabilizer;
    if Order(TheGroup)=8315553613086720000 then
      FuncInvariant:=function(Odisc, Linc)
        return MyFuncInvariant(Linc);
      end;
      FuncIsomorphy:=function(Linc1, Linc2)
        local Test1, Test2, TheRet;
        Test1:=IsItRegularSimplex(Linc1);
        Test2:=IsItRegularSimplex(Linc2);
        if Test1<>Test2 then
          Print("It is quite suprising to be there at all, please check\n");
          Print(NullMat(5));
        fi;
        if Test1=true then
          TheRet:=TestEquivalenceDelaunayMethod(Linc1, Linc2);
          if TheRet=false then
            return false;
          else
            return true;
          fi;
        else
          return RepresentativeAction(TheGroup, Linc1, Linc2, OnSets)<>fail;
        fi;
      end;
      FuncInvariantUpdate:=function(OdiscPrev, nbCall)
        return [];
      end;
      OrderLincStabilizer:=function(Linc)
        #return Order(StabilizerAntipodalMethod(Linc));
        return Order(Stabilizer(TheGroup, Linc, OnSets));
      end;
    elif Order(TheGroup)<=1000 then
      FuncInvariant:=function(Odisc, Linc)
        return Minimum(Orbit(TheGroup, Linc, OnSets));
      end;
      FuncIsomorphy:=function(Linc1, Linc2)
        return true;
      end;
      FuncInvariantUpdate:=function(OdiscPrev, nbCall)
        return [];
      end;
      OrderLincStabilizer:=function(Linc)
        return Order(Stabilizer(TheGroup, Linc, OnSets));
      end;
    else
      FuncInvariant:=function(Odisc, Linc)
        return __FuncInvariant(Odisc, Linc);
      end;
      FuncIsomorphy:=function(Linc1, Linc2)
        return RepresentativeAction(TheGroup, Linc1, Linc2, OnSets)<>fail;
      end;
      FuncInvariantUpdate:=function(OdiscPrev, NbCall)
        if NbCall=1001 then
          return GetDiscriminatingSet(TheGroup, NbCall);
        else
          return OdiscPrev;
        fi;
      end;
      OrderLincStabilizer:=function(Linc)
        return Order(Stabilizer(TheGroup, Linc, OnSets));
      end;
    fi;
    return OrbitGroupFormalism(Prefix, SavingTrigger,
        rec(FuncInvariant:=FuncInvariant,
            FuncIsomorphy:=FuncIsomorphy, 
            GroupOrder:=Order(TheGroup),
            OrderLincStabilizer:=OrderLincStabilizer, 
            FuncInvariantUpdate:=FuncInvariantUpdate));
  end;
  BankKeyInformation:=function(EXT, GroupExt)
    return rec(EXT:=EXT, Group:=GroupExt);
  end;
  BankCompleteInformation:=function(EXT, GroupExt, ListObject)
    return ListObject;
  end;
  BankGetVertexSet:=function(TheKey, TheComplete)
    return TheKey.EXT;
  end;
  BankGetGroup:=function(TheKey, TheComplete)
    return TheKey.Group;
  end;
  BankGetListObject:=function(TheComplete)
    return TheComplete;
  end;
  BankGetForIsom:=function(TheKey)
    return TheKey.EXT;
  end;
  return rec(
    Stabilizer:=OnSetsStabilizer,
    LiftingOrbits:=__LiftingOrbits,
    GroupUnion:=GroupUnion,
    ToPermGroup:=ToPermGroup,
    Order:=TheOrder,
    BankGetForIsom:=BankGetForIsom, 
    IsSubgroup:=OnSetsIsSubgroup,
    GroupConjugacy:=OnSetsGroupConjugacy,
    TransformIncidenceList:=OnSetsTransformIncidenceList, 
    OrbitGroupFormalism:=MyOrbitGroupFormalism,
    BankKeyInformation:=BankKeyInformation, 
    BankCompleteInformation:=BankCompleteInformation,
    BankGetVertexSet:=BankGetVertexSet, 
    BankGetGroup:=BankGetGroup, 
    BankGetListObject:=BankGetListObject);
end;



Data:=rec(TheDepth:=0,
          ThePath:=ThePath,
          IsBankSave:=IsBankSave,
          GetInitialRays:=GetInitialRays, 
          GroupFormalism:=MyPersoOnSetsGroupFormalism(), 
          DualDescriptionFunction:=__DualDescriptionLRS_Reduction,
          IsRespawn:=IsRespawn,
          Saving:=true,
          ThePathSave:=PathSave);





BankPath:=Concatenation(ThePathWork, "TheBank/");
Exec("mkdir -p ", BankPath);
DataBank:=rec(BankPath:=BankPath, Saving:=true);
BF:=BankRecording(DataBank, FuncStabilizer, FuncIsomorphy, FuncInvariant, MyPersoOnSetsGroupFormalism());

Print("Bank has been set up\n");


LORB:=__ListFacetByAdjacencyDecompositionMethod(FAC,
                                                PermGRP, 
                                                Data,
                                                BF);
SaveDataToFile("ListOrbitEXT", LORB);
