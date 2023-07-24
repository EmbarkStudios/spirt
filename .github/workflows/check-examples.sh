#!/usr/bin/env bash
set -e

# HACK(eddyb) `sed -E -z` expression to remove parts of the SPIR-T pretty-printing
# output that we don't want to be actaully shown in an example (in `README.md`).
spirt_cleanup_sed="\
    s/module\.(dialect|debug_info) = spv\.Module(\.DebugInfo)?\(.*\)\n\n//g;\
    s/\nexport \{\n(  [^\n]*\n)*\}//\
"

readme_examples=(
    tests/data/for-loop.wgsl.spvasm
)
for example in "${readme_examples[@]}"; do
    # Examples are kept in SPIR-V textual assembly form, so they first have to
    # be converted to binary SPIR-V, to be used with any other tooling.
    spirv-as "$example" -o "$example.spv"

    # Pretty-print the SPIR-T we get by lowering (and restructuring) the SPIR-V.
    cargo run --release --example spv-lower-print "$example.spv"

    # FIXME(eddyb) perhaps support picking which SPIR-T output gets used?
    example_spirt="$example.structured.spirt"

    old="$(
        grep -Pazo \
            "<!-- BEGIN $example_spirt -->\n[\`]{3}.*\n\K(.*\n)*(?=[\`]{3}\n<!-- END $example_spirt -->)" \
            README.md \
        | tr -d '\0'
    )" || (echo "README.md missing $example_spirt example!"; exit 1)
    new="$(sed -E -z "$spirt_cleanup_sed" < "$example_spirt")"
    diff -U3 <(echo "$old") <(echo "$new") || (
        echo -e "\n\nREADME.md example out of date: $example\n"
        echo -e "=== old version (from README.md) ===\n$old\n"
        echo -e "=== new version ===\n$new\n"
        echo "(for more information, see $0 script)"
        exit 1
    )
done
