#############################################################################
##
#W  props.gd
#Y  Copyright (C) 2014                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareProperty("IsSimpleDigraph", IsDigraph);
DeclareProperty("IsSymmetricDigraph", IsDigraph);
DeclareProperty("IsFunctionalDigraph", IsDigraph);
DeclareProperty("IsStronglyConnectedDigraph", IsDigraph);
DeclareProperty("IsAcyclicDigraph", IsDigraph);
DeclareProperty("IsTournament", IsDigraph);
DeclareProperty("IsEmptyDigraph", IsDigraphBySourceAndRange);
DeclareProperty("IsEmptyDigraph", IsDigraphByAdjacency);
DeclareProperty("IsEmptyDigraph", IsDigraph and HasNrEdges);
DeclareProperty("IsReflexiveDigraph", IsDigraph);