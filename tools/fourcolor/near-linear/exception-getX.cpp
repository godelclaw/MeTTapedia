PseudoConfiguration getX(void) {
    const PseudoConfiguration X = PseudoConfiguration::from_v_rotations(
        17,
        {{1, 2, 3, 4, 5, 6, 7, 8},
         {0, 8, 11, 12, 2},
         {0, 1, 12, -1, 3},
         {0, 2, -1, 13, 4},
         {0, 3, 13, 14, 5},
         {0, 4, 14, 15, 16, -1, 6},
         {0, 5, -1, 7},
         {0, 6, -1, 8},
         {0, 7, -1, 9, 10, 11, 1},
         {8, -1, 10},
         {8, 9, -1, 11},
         {1, 8, 10, -1, 12},
         {1, 11, -1, 2},
         {3, -1, 14, 4},
         {4, 13, -1, 15, 5},
         {5, 14, -1, 16},
         {5, 15, -1}},
        {Degree(8), Degree(5), Degree(5), Degree(5), Degree(5), Degree(7), Degree(5), Degree(5),
         Degree(7), Degree(5), Degree(5), Degree(8), Degree(5), Degree(5), Degree(8), Degree(5),
         Degree(5)});
    return X;
}
