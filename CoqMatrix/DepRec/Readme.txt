2021/6/19 11:40
1. Why this libray?
(1). An improvement/re-implementation of original Mat libray, which developed from NUAA
(2). Rename part of the name to standardize the naming style
(3). Create ListExt to organize all the things about list, and use standard library as much as possible
(4). Simplify the improvement
(5). Maintain maximum compatibility, such as "map : A -> B" and "map : A -> A", the compatibility of
	 the former is better.

2. Experience in proof
(1). Induction according to the main variable in the definition
(2). When multiple functions are nested, the outermost function is considered first.
(3). If the (1/2) principle conflicts, you need to consider (1) first.
	 At this time, the main variable may be a compound variable, and all the variables
	 in the inner layer can be summarized at the same time.
(4). A general principle is to simplify the complexity of expressions, including function
	 definitions and type definitions.

3. Records of name changes
NEW NAME				OLD NAME				FUNCTION DESCRIPTION			REMARK
-----------------		--------------------	-------------------------		--------------------
width                   width                   child lists have same length	an important predicate
map                     list_map                mapping of a list              	existed in std lib.
map_app                 list_map_app                                          	existed in std lib.
app_assoc               app_assoc                                              	existed in std lib.
app_nil_r               app_nil_r                                              	existed in std lib.
app_length              length_app                                            	existed in std lib. a bit different
app_length              height_mapp                                            	existed in std lib. a bit different
app_width               width_mapp              app width law
app_width               width_app												same thing, drop it.
app_comm_cons           cons_app                                              	existed in std lib.
rev_length              length_rev                                            	existed in std lib.
rev_unit                cons_rev                                              	existed in std lib.
rev_app_distr           rev_app                                                	existed in std lib.
list_app_dlist          list_app
lmap2                   list_each				mapping of two matrices
lmap2_app               --
lmap2_dnil_l            --
lmap2_tail              --
lmap2_length            list_each_length
lmap2_comm              list_each_comm											less assumptions
lmap2_assoc             list_each_assoc
ldot                    product'
ldot_comm               product'_comm											use l_map2_comm to do it
ldot_nil_r              product'_nil_r
ldot_to_list            map2_distr_l			dot distributed to mapping
ladd_zero_l             list_add_zero_l
ladd_zero_r             list_add_zero_r
lsub_zero_l             list_sub_zero_l
lsub_zero_r             list_sub_zero_r
lsub_comm               list_sub_opp			l1 - l2 = - (l2 - l1)
lsub_assoc1             list_sub_comm        	(l1 - l2) - l3 = (l1 - l3) - l2
lsub_assoc2             list_sub_assoc      	(l1 - l2) - l3 = l1 - (l2 + l3)
lsub_self               list_sub_self        	l - l = 0
lzero                   list_o              	a list all elements are 0
lzero_length            list_o_length
lunit                   list_i					a list only one elment is 1
lunit                   dlist_i'												less asumptions
lunit_length            length_list_i
lunit_n_0               list_i_n_0
dnil                    nil_list				a list of empty lists
dnil_height             height_nil_list
dnil_width              width_nil_list
dnil_app                nil_list_app
dnil_app                nil_list_mapp											duplicated
dnil_rev                rev_nil_list
dlist_h0_iff            height_dlist_0
dlist_w0_eq_dnil        width_dlist_0											a bit different
dlistappr               mapp                    append by rows					it is actually app in the std lib.
dlistappc               --                		append by columns
dlistmap                dlist_map            	mapping of a dlist				re-implemented
dlistmap_height         height_dlist_map                                      	a bit different
dlistmap_width          width_dlist_map                                        	stronger conclusion
dlistmap2_cons          mat_each'_cons
dlistmap2_app           mat_each'_app											simplifed proof
dlistmap2               mat_each'               mapping of two dlists			re-implemented
dlistmap2_height        height_mat_each'
dlistmap2_width         width_mat_each'
dlistmap2_comm          matrix_each'_comm
dlistmap2_assoc         matrix_each'_assoc
dlistmap2_dnil_l        mat_each'_nil_list_l
dlistmap2_tail          mat_each'_tail
dlistzero               dlist_o
dlistzero_height        dlist_o_height
dlistzero_width         dlist_o_width
dlistzero_w0_eq_dnil    dlist_o_m_0
dlistzero_app_row       list_o_app
dlistzero_app_col       --
dlistunit_height        height_dlist_i'
dlistunit_width         width_dlist_i'
dlistadd_zero_l         dlist_add_zero_l
dlistadd_zero_r         dlist_add_zero_r
dlistsub_comm           dlist_sub_opp			dl1 - dl2 = -(dl2 - dl1)		simplified proof
dlistsub_assoc2         dlist_sub_assoc      	(dl1-dl2)-dl3 = dl1-(dl2+dl3)   simplified proof
dlistsub_zero_l         dlist_sub_zero_l
dlistsub_zero_r         dlist_sub_zero_r
hdc                     headcolumn
hdc_length              length_headcolumn
tlc                     tailcolumn
dlist_trans             gettrans               transpose of dlist				different implementation: easy/difficult first/second
ldotdl                  l_mul_dl               list dot to dlist one-by-one
dldotdl                 dl_mul_dl              dlist dot to dlist one-by-one

mmapdl                  matrix_map'            mapping a matrix to dlist
mmapdl_height           height_matrix_map
mmapdl_width            width_matrix_map
mmapdl_sub_comm         matrix_sub_opp
mmap2dl                 mat_each           
mmap2dl_height          height_mat_each
mmap2dl_width           width_mat_each
mmap                    matrix_map			   mapping a matrix
mmap_mor                mat_map_mor            mmap is proper morphism			simplified proof
mmap2                   matrix_each            mapping two matrices
mmap2_compat            matrix_each_compat
mmap2_comm              matrix_comm
mmap2_assoc             matrix_assoc
mmap2_mor               mat_each_mor        

mat0 					MO
mat1                 	MI

madd_zero_l             matrix_add_zero_l
madd_zero_r             matrix_add_zero_r
				    	
msub_comm               matrix_sub_opp
msub_assoc2             matrix_sub_assoc    (m1 - m2) - m3 = m1 - (m2 + m3)
msub_zero_l             matrix_sub_zero_l
msub_zero_r             matrix_sub_zero_r
msub_self               matrix_sub_self
											    	
mmul_data               mat_mul_mat          
mmul_add_distr_l        matrix_mul_distr_l
mmul_add_distr_r        matrix_mul_distr_r
mcmul                   const_mul_l          c * M
mmulc                   const_mul_r          M * c
