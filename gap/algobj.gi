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
Unbind(DigraphColouringAlgorithmFamilyObj);
