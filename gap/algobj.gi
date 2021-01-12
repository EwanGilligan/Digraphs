# Global bindings used for graph colouring algorithm selection.
DigraphColouringAlgorithmFamilyObj := NewFamily(
                                      "DigraphColouringAlgorithmFamily",
                                      IsDigraphAlgorithm,
                                      IsDigraphColouringAlgorithm);
BindGlobal("DigraphColouringAlgorithmLawler",
            Objectify(
              NewType(
                DigraphColouringAlgorithmFamilyObj,
                IsDigraphColouringAlgorithmLawler),
              rec()));
BindGlobal("DigraphColouringAlgorithmByskov",
            Objectify(
              NewType(
                DigraphColouringAlgorithmFamilyObj,
                IsDigraphColouringAlgorithmByskov),
              rec()));
BindGlobal("DigraphColouringAlgorithmZykov",
            Objectify(
              NewType(
                DigraphColouringAlgorithmFamilyObj,
                IsDigraphColouringAlgorithmZykov),
              rec()));
Unbind(DigraphColouringAlgorithmFamilyObj);
