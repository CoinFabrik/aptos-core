module 0xc0ffee::m {

    public fun test1(x: u64) {
        if (x % x == 2) {
            abort 1;
        };
        if (x ^ x == 2) {
            abort 1;
        };
        if (x <= x) {
            abort 1;
        };
        if (x >= x) {
            abort 1;
        };
        if (x == x) {
            abort 1;
        };
        if (x | x == 2) {
            abort 1;
        };
        if (x & x == 2) {
            abort 1;
        };
        if (x / x == 2) {
            abort 1;
        };
        if (x != x) {
            abort 1;
        };
        if (x < x) {
            abort 1;
        };
        if (x > x) {
            abort 1;
        };
    }

}
