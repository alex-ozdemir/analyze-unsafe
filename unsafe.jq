def is_block: objects | has("unsafe_points");

def is_unsafe_block: is_block and .unsaf;

def is_safe_block: is_block and (.unsaf | not);

def is_use: has("item") and (.item == "Deref" or .item.variant == "Call");

def is_deref: is_use and (.item == "Deref");

def is_call: is_use and (.item.variant? == "Call");

def get_child_blocks: select(is_block) | .unsafe_points | map(.item?) | map(select(.variant? == "Block")) | map(.fields | .[0]) | select(length > 0) | .[];

def get_safe_child_blocks: get_child_blocks | select(is_safe_block);

def get_shallow_uses: .unsafe_points | .[] | select(is_use);

def get_own_uses: recurse(get_child_blocks; is_safe_block) | get_shallow_uses;

def blocks: paths as $path | getpath($path) | objects | select(is_block) ;

def block_has_only_ffi: .unsafe_points | paths;

# .[] | blocks | get_shallow_uses as $uses | select($uses | length > 0)

.[] | blocks | select(is_unsafe_block) | get_own_uses | select(is_deref)
