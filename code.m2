-- implementation of the recursive algorithm computing the facet complexity of a reflexive polytope

needsPackage "ReflexivePolytopesDB"
needsPackage "Polyhedra"
needsPackage "NormalToricVarieties"

affineDim = method()
affineDim List := L ->(
    if #L == 0 then
        return 0;
    LReduced = apply(L, i-> i - first L);
    r = rank matrix LReduced;
    return r
)
affineDim Matrix := M ->(
    columnDimension = numgens source M;
    if columnDimension == 0 then
        return 0;
    MReduced = M - matrix {columnDimension:M_0} ;
    r = rank MReduced;
    return r
)

facetComplexityRecursive = method()
facetComplexityRecursive (Polyhedron, List, List, List) := (P, VList, FList, SList) ->(
    facets := FList;
    d := ambDim P;
    pRank := 0;
    if #SList == #VList then
        return 0
    else (
        facetsRemaining := select(facets, i->not isSubset(i, SList));
        pRank = min apply(facetsRemaining, f->(
            accRank := affineDim VList_(select(f, i->member(i,SList)));
            if accRank >= d - 2 then d - 1 - accRank  + facetComplexityRecursive(P, VList, FList, sort unique join(SList,f)) 
            else 100
            )
        );
    );
    return pRank
)
-- M2 memoization; each polytope will have its own cache 
facetComplexityRecursive = memoize facetComplexityRecursive 


facetComplexity = P ->(
    E := P;
    assert(isReflexive E);
    VList = entries transpose vertices E;
    FList := apply(faces(1,E) , k->first k);
    rho := min apply(FList, f-> facetComplexityRecursive(E, VList, FList, f));
    rho
)

-- #######  example 1 #######
-- use Kreuzer-Skarke's Palp data;
kspolys = kreuzerSkarkeDim3();
P = convexHull matrix kspolys#4309 -- Example 3.15
vertices P
isReflexive P
fVector P

-- the facetComplexity rho'
facetComplexity P

-- Picard rank via the toric variety
rank picardGroup normalToricVariety polar P