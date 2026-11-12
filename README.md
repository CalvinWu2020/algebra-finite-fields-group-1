# Algebra finite fields

Prime and extension fields using polynomial modular arithmetic.

```cmake
include(FetchContent)

FetchContent_Declare(
    algebra_finite_fields
    GIT_REPOSITORY git@github.com:CalvinWu2020/algebra-finite-fields-group-1.git
)

FetchContent_MakeAvailable(algebra_finite_fields)

target_link_libraries(my_app PRIVATE algebra::finite_fields)
```
