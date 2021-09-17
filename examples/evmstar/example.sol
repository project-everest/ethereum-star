contract Test {
    uint n = 10;
    
    function Test() {
        n = 0;
    }
    
    function IncrBy(uint m) returns (uint r) {
        n = n+m;
        return n;
    }
}