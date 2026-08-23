(program
  1.0.0
  (lam
    datum
    (lam
      redeemer
      (lam
        context
        [(lam
           sum_amounts
           [(lam
              count_items
              [(lam
                 join_names
                 [(lam
                    scale
                    [(lam
                       is_zero
                       [(lam
                          vault_fields
                          [(lam
                             owner
                             [(lam
                                total
                                [(lam
                                   redeemer_pair
                                   [(lam
                                      redeemer_tag
                                      [(lam
                                         redeemer_fields
                                         (force
                                           [[[(force (builtin ifThenElse))
                                               [[ (builtin equalsInteger) redeemer_tag ]
                                                 (con integer 0)
                                               ]
                                             ]
                                              (delay
                                                [(lam
                                                   amount
                                                   [(lam
                                                      recipient
                                                      [(lam
                                                         fee
                                                         [(lam
                                                            label
                                                            (force
                                                              [[[(force
                                                                   (builtin ifThenElse)
                                                                 )
                                                                  [[(builtin
                                                                      lessThanInteger
                                                                    )
                                                                     (con integer 0)
                                                                   ]
                                                                    amount
                                                                  ]
                                                                ]
                                                                 (delay
                                                                   (force
                                                                     [[[(force
                                                                          (builtin
                                                                            ifThenElse
                                                                          )
                                                                        )
                                                                         [[(builtin
                                                                             lessThanEqualsInteger
                                                                           )
                                                                            fee
                                                                          ]
                                                                           total
                                                                         ]
                                                                       ]
                                                                        (delay
                                                                          (force
                                                                            [[[(force
                                                                                 (builtin
                                                                                   ifThenElse
                                                                                 )
                                                                               )
                                                                                [is_zero
                                                                                  (con
                                                                                    integer
                                                                                    0
                                                                                  )
                                                                                ]
                                                                              ]
                                                                               (delay
                                                                                 (force
                                                                                   [[[(force
                                                                                        (builtin
                                                                                          ifThenElse
                                                                                        )
                                                                                      )
                                                                                       [[(builtin
                                                                                           equalsByteString
                                                                                         )
                                                                                          label
                                                                                        ]
                                                                                         recipient
                                                                                       ]
                                                                                     ]
                                                                                      (delay
                                                                                        (error
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                     (delay
                                                                                       (con
                                                                                         unit
                                                                                         ()
                                                                                       )
                                                                                     )
                                                                                   ]
                                                                                 )
                                                                               )
                                                                             ]
                                                                              (delay
                                                                                (force
                                                                                  [[[(force
                                                                                       (builtin
                                                                                         ifThenElse
                                                                                       )
                                                                                     )
                                                                                      [[(builtin
                                                                                          equalsByteString
                                                                                        )
                                                                                         label
                                                                                       ]
                                                                                        label
                                                                                      ]
                                                                                    ]
                                                                                     (delay
                                                                                       (error
                                                                                       )
                                                                                     )
                                                                                   ]
                                                                                    (delay
                                                                                      (con
                                                                                        unit
                                                                                        ()
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                       (delay (error))
                                                                     ]
                                                                   )
                                                                 )
                                                               ]
                                                                (delay (error))
                                                              ]
                                                            )
                                                          )
                                                           [[(builtin appendByteString)
                                                              owner
                                                            ]
                                                             (con bytestring #5641554c54)
                                                           ]
                                                         ]
                                                       )
                                                        [[ (builtin divideInteger) amount ]
                                                          (con integer 10)
                                                        ]
                                                      ]
                                                    )
                                                     [(builtin unBData)
                                                       [(force (builtin headList))
                                                         [(force (builtin tailList))
                                                           redeemer_fields
                                                         ]
                                                       ]
                                                     ]
                                                   ]
                                                 )
                                                  [(builtin unIData)
                                                    [(force (builtin headList))
                                                      redeemer_fields
                                                    ]
                                                  ]
                                                ]
                                              )
                                            ]
                                             (delay
                                               (force
                                                 [[[(force (builtin ifThenElse))
                                                     [[(builtin equalsInteger)
                                                        redeemer_tag
                                                      ]
                                                       (con integer 1)
                                                     ]
                                                   ]
                                                    (delay
                                                      [(lam
                                                         context_fields
                                                         [(lam
                                                            entries
                                                            [(lam
                                                               recorded
                                                               [(lam
                                                                  budget
                                                                  (force
                                                                    [[[(force
                                                                         (builtin
                                                                           ifThenElse
                                                                         )
                                                                       )
                                                                        [[(builtin
                                                                            equalsInteger
                                                                          )
                                                                           [[(builtin
                                                                               addInteger
                                                                             )
                                                                              [sum_amounts
                                                                                entries
                                                                              ]
                                                                            ]
                                                                             [sum_amounts
                                                                               recorded
                                                                             ]
                                                                           ]
                                                                         ]
                                                                          budget
                                                                        ]
                                                                      ]
                                                                       (delay
                                                                         (force
                                                                           [[[(force
                                                                                (builtin
                                                                                  ifThenElse
                                                                                )
                                                                              )
                                                                               [[(builtin
                                                                                   lessThanInteger
                                                                                 )
                                                                                  (con
                                                                                    integer
                                                                                    0
                                                                                  )
                                                                                ]
                                                                                 [count_items
                                                                                   entries
                                                                                 ]
                                                                               ]
                                                                             ]
                                                                              (delay
                                                                                (con
                                                                                  unit
                                                                                  ()
                                                                                )
                                                                              )
                                                                            ]
                                                                             (delay (error))
                                                                           ]
                                                                         )
                                                                       )
                                                                     ]
                                                                      (delay (error))
                                                                    ]
                                                                  )
                                                                )
                                                                 [ scale total ]
                                                               ]
                                                             )
                                                              [[(force (builtin mkCons))
                                                                 [ (builtin iData) total ]
                                                               ]
                                                                [[(force (builtin mkCons))
                                                                   [(builtin iData)
                                                                     (con integer 1)
                                                                   ]
                                                                 ]
                                                                  (con (list data) [  ])
                                                                ]
                                                              ]
                                                            ]
                                                          )
                                                           [(builtin unListData)
                                                             [(force (builtin headList))
                                                               context_fields
                                                             ]
                                                           ]
                                                         ]
                                                       )
                                                        [(force (force (builtin sndPair)))
                                                          [ (builtin unConstrData) context ]
                                                        ]
                                                      ]
                                                    )
                                                  ]
                                                   (delay
                                                     [(lam
                                                        extra
                                                        [(lam
                                                           witnesses
                                                           [(lam
                                                              joined
                                                              (force
                                                                [[[(force
                                                                     (builtin ifThenElse)
                                                                   )
                                                                    [[(builtin
                                                                        lessThanInteger
                                                                      )
                                                                       total
                                                                     ]
                                                                      [[(builtin addInteger)
                                                                         total
                                                                       ]
                                                                        extra
                                                                      ]
                                                                    ]
                                                                  ]
                                                                   (delay
                                                                     (force
                                                                       [[[(force
                                                                            (builtin
                                                                              ifThenElse
                                                                            )
                                                                          )
                                                                           [[(builtin
                                                                               equalsByteString
                                                                             )
                                                                              [[[(builtin
                                                                                   sliceByteString
                                                                                 )
                                                                                  (con
                                                                                    integer
                                                                                    0
                                                                                  )
                                                                                ]
                                                                                 [(builtin
                                                                                    lengthOfByteString
                                                                                  )
                                                                                   owner
                                                                                 ]
                                                                               ]
                                                                                joined
                                                                              ]
                                                                            ]
                                                                             owner
                                                                           ]
                                                                         ]
                                                                          (delay
                                                                            (con unit ())
                                                                          )
                                                                        ]
                                                                         (delay (error))
                                                                       ]
                                                                     )
                                                                   )
                                                                 ]
                                                                  (delay (error))
                                                                ]
                                                              )
                                                            )
                                                             [ join_names witnesses ]
                                                           ]
                                                         )
                                                          [(builtin unListData)
                                                            [(force (builtin headList))
                                                              [(force (builtin tailList))
                                                                redeemer_fields
                                                              ]
                                                            ]
                                                          ]
                                                        ]
                                                      )
                                                       [(builtin unIData)
                                                         [(force (builtin headList))
                                                           redeemer_fields
                                                         ]
                                                       ]
                                                     ]
                                                   )
                                                 ]
                                               )
                                             )
                                           ]
                                         )
                                       )
                                        [ (force (force (builtin sndPair))) redeemer_pair ]
                                      ]
                                    )
                                     [ (force (force (builtin fstPair))) redeemer_pair ]
                                   ]
                                 )
                                  [ (builtin unConstrData) redeemer ]
                                ]
                              )
                               [(builtin unIData)
                                 [(force (builtin headList))
                                   [ (force (builtin tailList)) vault_fields ]
                                 ]
                               ]
                             ]
                           )
                            [(builtin unBData)
                              [ (force (builtin headList)) vault_fields ]
                            ]
                          ]
                        )
                         [(force (force (builtin sndPair)))
                           [ (builtin unConstrData) datum ]
                         ]
                       ]
                     )
                      (lam n [ [ (builtin equalsInteger) n ] (con integer 0) ])
                    ]
                  )
                   (lam n [ [ (builtin multiplyInteger) n ] (con integer 2) ])
                 ]
               )
                [(lam
                   step_fn
                   [(lam self [ step_fn (lam value [ [ self self ] value ]) ])
                     (lam self [ step_fn (lam value [ [ self self ] value ]) ])
                   ]
                 )
                  (lam
                    recurse
                    (lam
                      items
                      (force
                        [[[ (force (force (builtin chooseList))) items ]
                           (delay (con bytestring #))
                         ]
                          (delay
                            [[(builtin appendByteString)
                               [ (builtin unBData) [ (force (builtin headList)) items ] ]
                             ]
                              [ recurse [ (force (builtin tailList)) items ] ]
                            ]
                          )
                        ]
                      )
                    )
                  )
                ]
              ]
            )
             [(lam
                step_fn
                [(lam self [ step_fn (lam value [ [ self self ] value ]) ])
                  (lam self [ step_fn (lam value [ [ self self ] value ]) ])
                ]
              )
               (lam
                 recurse
                 (lam
                   items
                   (force
                     [[[ (force (force (builtin chooseList))) items ]
                        (delay (con integer 0))
                      ]
                       (delay
                         [[ (builtin addInteger) (con integer 1) ]
                           [ recurse [ (force (builtin tailList)) items ] ]
                         ]
                       )
                     ]
                   )
                 )
               )
             ]
           ]
         )
          [(lam
             step_fn
             [(lam self [ step_fn (lam value [ [ self self ] value ]) ])
               (lam self [ step_fn (lam value [ [ self self ] value ]) ])
             ]
           )
            (lam
              recurse
              (lam
                items
                (force
                  [[[ (force (force (builtin chooseList))) items ]
                     (delay (con integer 0))
                   ]
                    (delay
                      [[(builtin addInteger)
                         [ (builtin unIData) [ (force (builtin headList)) items ] ]
                       ]
                        [ recurse [ (force (builtin tailList)) items ] ]
                      ]
                    )
                  ]
                )
              )
            )
          ]
        ]
      )
    )
  )
)
