### Verification

```bash
verus --crate-type=lib --expand-errors verge_lib/verge.rs
```

### Compilation

```bash
verus --crate-type=lib --export libverge.meta --compile verge_lib/verge.rs 
```
