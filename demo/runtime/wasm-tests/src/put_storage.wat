(module
    ;; ext_set_storage(
    ;;     location_ptr: i32,
    ;;     value_non_null: bool,  // Optimization, we can use len == MAX_LEN
    ;;     value_ptr: i32,
    ;; )
    (import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
    (import "env" "memory" (memory 1))

    (func (export "call")
        (call $ext_set_storage
            (i32.const 4)  ;; Pointer to a location of the storage.
            (i32.const 1)  ;; Value is not null.
            (i32.const 36) ;; Pointer to a data we want to put in the storage.
        )
    )

    ;; Location of storage to put the data. 32 bytes.
    (data (i32.const 4) "\ea\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\01")

    ;; The test data we want to write. 32 bytes.
    (data (i32.const 36) "\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa\aa")
)
