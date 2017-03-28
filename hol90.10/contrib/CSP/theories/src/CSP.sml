(*****************************************************************************
 * Builds the top theory for the CSP library. All the definitions and theorems
 * in the library will be accessible through the ancestors of "CSP".
 * The development looks like this (thanks to Brian Graham for the 
 * picture):
 * 
 * 
 *                    set                    string
 *                     |                       |
 *                     `-----------v-----------'
 *                                 |
 *                              CSP_base
 *                                 |
 *                       ,---------^----------------.
 *                       |                          |
 *                   list_lib1                 boolarith1
 *                       |                          |
 *                    traces                   boolarith2
 *                       |                          |
 *                       `---------v----------------'
 *                                 |
 *                               restrict
 *                                 |
 *                 ,--------------'|
 *                 |               |
 *               order           star
 *                 |               |      
 *  .--------------'           process_ty
 *  |                              |
 *  |      ,----------,--------,---^---.---------.----------.
 *  |      |          |        |       |         |          |
 *  |    stop        run    prefix   after    choice    parallel 
 *  |      |          |        |       |         |          |
 *  | process_fix     |        |       |         |          |
 *  |      |          |        |       |         |          |
 *  |      mu         |        |       |         |          |
 *  |      |          |        |       |         |          |
 *  |      `----------`--------`---v---'---------'----------'
 *  |                              |
 *  |                           process
 *  |                              |
 *  |           ,------------------^-----------------.
 *  |           |                  |                 |        
 *  |       csp_syntax        after_laws          par_laws
 *  |           |                  |                 |
 *  `-----------`------------------v-----------------'
 *                                 |
 *                                CSP
 * 
 * 
 **********************************************************************)
new_theory "CSP";

map new_parent ["csp_syntax", "after_laws", "par_laws", "order"];

close_theory();
export_theory();
