#############################################################################
##
#W  bliss.gi
#Y  Copyright (C) 2014                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# methods using bliss . . . 

# none of these methods applies to multigraphs

InstallMethod(DigraphCanonicalLabelling, "for a digraph",
[IsDigraph], 
function(graph)

  if IsMultiDigraph(graph) then 
    Error("Digraphs: DigraphCanonicalLabelling: usage,\n",
          "not yet implemented,\n");
  fi;
  return DIGRAPH_CANONICAL_LABELING(graph);
end);

#

InstallMethod(IsIsomorphicDigraph, "for digraphs",
[IsDigraph, IsDigraph],
function(g1, g2)
  
  # check some invariants
  if DigraphNrVertices(g1) <> DigraphNrVertices(g2) 
    or DigraphNrEdges(g1)  <> DigraphNrEdges(g2) 
    or IsMultiDigraph(g1)  <> IsMultiDigraph(g2)    then 
    return false;
  fi; #JDM more!

  if IsMultiDigraph(g1) then 
    Error("Digraphs: DigraphCanonicalLabelling: usage,\n",
          "not yet implemented,\n");
  fi;
  
  return DigraphRelabel(g1, DigraphCanonicalLabelling(g1)) 
    = DigraphRelabel(g2, DigraphCanonicalLabelling(g2));
end);

#

InstallMethod(AutomorphismGroup, "for a digraph",
[IsDigraph],
function(graph)
  local x;
  
  if IsMultiDigraph(graph) then 
    Error("Digraphs: DigraphCanonicalLabelling: usage,\n",
          "not yet implemented,\n");
  fi;
  
  x := DIGRAPH_AUTOMORPHISMS(graph);
  SetDigraphCanonicalLabelling(graph, x[1]);
  
  if IsEmpty(x[2]) then 
    return Group(());
  else 
    return Group(x[2]);
  fi;
end);

#

InstallMethod(DigraphIsomorphism, "for two digraphs",
[IsDigraph, IsDigraph],
function(g1, g2)
  
  if not IsIsomorphicDigraph(g1, g2) then 
    return fail;
  fi;
  
  return DigraphCanonicalLabelling(g1)/DigraphCanonicalLabelling(g2);
end);

#EOF