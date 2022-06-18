use proc_macro2::Span;
use venial::Punctuated;

use super::{
    attr::{Attr, EnumAttrs, RenameAllAttr},
    case::RenameRule,
};

pub fn get_rename_rule(input: &ItemEnum) -> Result<RenameRule, venial::Error> {
    let rules: Vec<_> = input
        .attributes
        .iter()
        .filter(|attr| attr.path.is_ident("ruma_enum"))
        .map(|attr| attr.parse_args::<RenameAllAttr>().map(RenameAllAttr::into_inner))
        .collect::<Result<_, venial::Error>>()?;

    match rules.len() {
        0 => Ok(RenameRule::None),
        1 => Ok(rules[0]),
        _ => Err(venial::Error::new_at_span(
            Span::call_site(),
            "found multiple ruma_enum(rename_all) attributes",
        )),
    }
}

pub fn get_enum_attributes(input: &Variant) -> Result<EnumAttrs, venial::Error> {
    let mut attributes = EnumAttrs::default();

    for attr in &input.attrs {
        if !attr.path.is_ident("ruma_enum") {
            continue;
        }

        let enum_attrs = attr.parse_args_with(Punctuated::<_>::parse_terminated)?;
        for enum_attr in enum_attrs {
            match enum_attr {
                Attr::Rename(s) => {
                    if attributes.rename.is_some() {
                        return Err(venial::Error::new_at_span(
                            Span::call_site(),
                            "found multiple ruma_enum(rename) attributes",
                        ));
                    }
                    attributes.rename = Some(s);
                }
                Attr::Alias(s) => {
                    attributes.aliases.push(s);
                }
            }
        }
    }

    Ok(attributes)
}
