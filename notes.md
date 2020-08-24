Random theorizing about syntax:

```
fn debug value;
  match known(value).type;
    struct(fields) =>
      for key in fields;
        print("#{key}: #{value[key]}")
    nat(n) => print(n)
    bool(b) => print(b)
```
