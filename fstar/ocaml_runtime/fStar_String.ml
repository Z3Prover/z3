let list_of_string (s : string) : FStar_Char.char list =
  let rec collect index chars =
    if index = String.length s then List.rev chars
    else
      let decoded = String.get_utf_8_uchar s index in
      let c = Uchar.to_int (Uchar.utf_decode_uchar decoded) in
      collect (index + Uchar.utf_decode_length decoded) (c :: chars)
  in
  collect 0 []

let string_of_list (chars : FStar_Char.char list) : string =
  let buffer = Buffer.create (List.length chars) in
  List.iter (fun c -> Buffer.add_utf_8_uchar buffer (Uchar.of_int c)) chars;
  Buffer.contents buffer
